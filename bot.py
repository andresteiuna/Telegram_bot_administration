# -*- coding: utf-8 -*-
# bot_ia.py

# Requisitos:
# pip install python-telegram-bot[job-queue] asyncssh pytz
# En el servidor remoto (192.168.1.100):
# - Suricata configurado y ejecutándose, cargando tus reglas en local.rules (o custom.rules).
# - Reglas Suricata: Asegúrate de tener las reglas con SIDs 1000001 a 1000009 (o más si añadiste HTTPS).
# - Usuario SSH (definido en REMOTE_USER) con acceso al servidor.
# - Permisos sudo para el usuario SSH para ejecutar:
#   - iptables
#   - ss
#   - el script de investigación web (si lo usas)
#   - mkdir -p para el directorio del log automático
#   - touch para el archivo del log automático
#   - chown para el archivo del log automático (opcional, si cambias LOG_FILE_PATH)
# - Crear el script de investigación web si usas esa opción de mitigación (ej: /opt/bot_scripts/investigate_web.sh)

import sys
import spacy
import asyncssh
import asyncio
import socket
import json # Importar la librería json
from telegram import Update
from telegram.constants import ParseMode
# Importar ConversationHandler
from telegram.ext import Application, CommandHandler, MessageHandler, filters, ContextTypes, CallbackQueryHandler, JobQueue, ConversationHandler
from telegram import InlineKeyboardButton, InlineKeyboardMarkup
import re
from collections import defaultdict
from datetime import datetime, timedelta, timezone # Importar timezone
import pytz
import hashlib

# Cargar el modelo de spaCy para español (comentado como en el original)
# try:
#     nlp = spacy.load("es_core_news_md")
#     print("Modelo de spaCy cargado exitosamente.")
# except OSError:
#     print("Advertencia: Modelo de spaCy 'es_core_news_md' no encontrado. La detección de lenguaje natural será básica.")
#     nlp = None

# Definir los comandos y sus respuestas
COMANDOS = {
    'ip': 'hostname -I',
    'conexion': 'ping -c 4 8.8.8.8',
    'reboot': 'sudo reboot',
    'poweroff': 'sudo poweroff',
    'memoria': 'free -h',
    'disco': 'df -h',
    'uptime': 'uptime -p',
    'exec': 'echo "No se especificó un comando para ejecutar"',
    'accesos': 'tail -n 50 /var/log/auth.log | grep "Accepted publickey"',
    'alertas': 'awk \'$1 >= strftime("%m/%d/%Y-%H:%M:%S", systime() - 3600)\' /var/log/suricata/fast.log | grep -E "\\[\\*\\*\\]"',
    'ping': 'ping -c 4 {ip}',
    'network_status': 'ip a',
    'memory_usage': 'free -h',
    'disk_usage': 'df -h',
    'run_web_script': 'sudo /opt/bot_scripts/investigate_web.sh {ip}',
    'unblock_ip_cmd': 'sudo iptables -D INPUT -s {ip} -j DROP'
}

# ESTRUCTURA PARA LA DESCRIPCIÓN DE COMANDOS CATEGORIZADOS
COMANDOS_DESCRIPCION_CATEGORIZED = {
    "Comandos Básicos": [
        ("/start", "Muestra este mensaje de ayuda"),
        ("/cancelar", "Cancela el proceso actual (ej. añadir IP de excepción)") # Añadido
    ],
    "Control del Servidor": [
        ("/reiniciar", "Reinicia el servidor remoto"),
        ("/apagar", "Apaga el servidor remoto")
    ],
    "Estado del Sistema": [
        ("/check", "Comprueba si el servidor está encendido"),
        ("/uptime", "Muestra el tiempo de actividad del sistema"),
        ("/memory_usage", "Muestra el uso de memoria"),
        ("/disk_usage", "Muestra el uso de disco")
    ],
    "Red y Conectividad": [
        ("/network_status", "Muestra información de red (IP, gateway, DNS)"),
        ("/ping <IP o dominio>", "Realiza un ping desde el servidor remoto")
    ],
    "Seguridad y Logs": [
        ("/accesos", "Muestra los últimos accesos SSH"),
        ("/alertas", "Muestra las últimas alertas de Suricata (última hora)"),
        ("/mitigar", "Muestra las alertas recientes para gestión (bloqueo de IP u otras acciones)"),
        ("/modo_automatico", "Activa/Desactiva el modo de mitigación automática para ciertas alertas."),
        ("/desbloquear <IP>", "Desbloquea una IP que fue bloqueada por el bot."),
        ("/excepciones", "Muestra y gestiona las IPs de excepción para las alertas.") # Añadir descripción
    ],
    "Ejecución Remota": [
        ("/exec <comando>", "Ejecuta un comando en el servidor remoto")
    ]
}

TOKEN = 'TOKEN_TELEGRAM'
REMOTE_USER = 'root'
REMOTE_HOST = '192.168.1.100'

recent_alerts = {}
blocked_ips = set()
exception_ips = set() # <-- Añadido: Conjunto para IPs de excepción

# --- Variables para el Modo Automático ---
is_auto_mode_active = False
auto_mode_start_time = None
processed_alerts_in_session = set()
# Mantener la misma ruta de log, pero ahora escribiremos JSON
LOG_FILE_PATH = "/var/log/bot_auto_actions.log"
auto_mode_chat_id = None
# --- Fin Variables Modo Automático ---

# Define server timezone (assuming UTC based on the 2-hour offset observation)
SERVER_TZ = pytz.timezone('UTC')
MADRID_TZ = pytz.timezone('Europe/Madrid')

# Define los estados para la conversación de añadir excepción de IP
ASK_FOR_IP = 1 # <-- Añadido: Estado para la conversación de excepciones

# --- Conexión SSH Persistente ---
persistent_ssh_conn = None

async def connect_ssh():
    """Establece y gestiona la conexión SSH persistente."""
    global persistent_ssh_conn
    if persistent_ssh_conn is None or not persistent_ssh_conn.is_connected():
        print(f"Intentando establecer conexión SSH a {REMOTE_HOST}...")
        try:
            conn = await asyncssh.connect(REMOTE_HOST, username=REMOTE_USER, connect_timeout=10)
            print("Conexión SSH establecida.")
            persistent_ssh_conn = conn
            return conn
        except asyncssh.Error as e:
            print(f"ERROR al establecer conexión SSH: {e}")
            persistent_ssh_conn = None
            raise
        except Exception as e:
            print(f"ERROR inesperado al establecer conexión SSH: {e}")
            persistent_ssh_conn = None
            raise

# --- Helper para ejecutar comandos remotos ---
async def run_remote_command(command: str):
    """Ejecuta un comando en el servidor remoto a través de la conexión SSH persistente."""
    global persistent_ssh_conn
    try:
        if persistent_ssh_conn is None:
             # print("Debug run_remote_command: persistent_ssh_conn is None, attempting connect_ssh()...") # Debug print
             await connect_ssh()

        conn = persistent_ssh_conn
        # print(f"Debug run_remote_command: Using SSH connection: {conn}") # Debug print

        # print(f"Debug run_remote_command: Running command: {command}") # Debug print
        result = await conn.run(command, check=True, timeout=30)
        # print(f"Debug run_remote_command: Command finished.") # Debug print
        return result.stdout.strip()

    except asyncssh.ProcessError as e:
        # print("Debug run_remote_command: Caught ProcessError.") # Debug print
        return f"Error ejecutando el comando '{command}':\n{e.stdout.strip()}\n{e.stderr.strip()}"
    except asyncssh.TimeoutError:
         # print("Debug run_remote_command: Caught TimeoutError.") # Debug print
         return f"Error ejecutando el comando '{command}': Tiempo de espera agotado."
    except asyncssh.Error as e:
         # Capturar otros errores de SSH (ej. conexión perdida, autenticación)
         # print(f"Debug run_remote_command: Caught asyncssh.Error: {e}") # Debug print
         print(f"ERROR SSH durante la ejecución del comando '{command}': {e}")
         persistent_ssh_conn = None
         return f"Error de conexión SSH durante la ejecución del comando '{command}': {e}"
    except Exception as e:
        # Capturar cualquier otro error inesperado
        # print(f"Debug run_remote_command: Caught unexpected Exception: {e}") # Debug print
        print(f"ERROR inesperado al ejecutar el comando '{command}': {e}")
        return f"Error inesperado al ejecutar el comando '{command}': {e}"

# --- Helper para cerrar la conexión persistente ---
async def close_persistent_ssh_connection(application: Application):
    """Cierra la conexión SSH persistente al apagar el bot."""
    global persistent_ssh_conn
    if persistent_ssh_conn and persistent_ssh_conn.is_connected():
        print("Cerrando conexión SSH persistente...")
        try:
            persistent_ssh_conn.close()
            await asyncio.sleep(0.1)
            if not persistent_ssh_conn.is_connected():
                print("Conexión SSH persistente cerrada.")
            else:
                print("La conexión SSH persistente podría no haberse cerrado completamente.")
        except Exception as e:
            print(f"Error mientras se intentaba cerrar la conexión SSH: {e}")
    persistent_ssh_conn = None

# --- Helper para escapar caracteres problemáticos para Markdown V2 ---
def escape_markdown(text: str) -> str:
    """Escapa caracteres especiales de MarkdownV2."""
    escape_chars = r'_*[]()~`>#+-=|{}.!'
    text = str(text)
    # Escapar la barra invertida primero
    text = text.replace('\\', '\\\\')
    for char in escape_chars:
        text = text.replace(char, f'\\{char}')
    return text

# --- Helper para escapar texto para usarlo dentro de un comando shell echo (especialmente dentro de comillas dobles) ---
def shell_escape_log_data(text):
    """Escapa texto para que sea seguro usarlo dentro de comillas dobles en un comando shell echo."""
    text = str(text)
    text = text.replace('\\', '\\\\') # Escapar la barra invertida primero
    text = text.replace('"', '\\"')   # Escapar comillas dobles
    text = text.replace('$', '\\$')   # Escapar signo de dólar
    text = text.replace('`', '\\`')   # Escapar backticks
    return text

# --- NUEVA FUNCIÓN: Log mitigation action in JSON format ---
async def log_mitigation_action(action_data: dict):
    """Logs a mitigation action as a JSON object to the remote log file."""
    log_entry = action_data.copy()
    # Usar datetime.now(timezone.utc) para obtener la hora actual en UTC con información de zona horaria
    log_entry['@timestamp'] = datetime.now(timezone.utc).isoformat()

    # Asegurarse de que todos los valores sean strings para evitar problemas con json.dumps y tipos complejos
    for key, value in log_entry.items():
        log_entry[key] = str(value)

    json_log_line = json.dumps(log_entry)
    # Usamos shell_escape_log_data para escapar el string JSON completo antes de ponerlo en el comando echo
    log_command = f'echo "{shell_escape_log_data(json_log_line)}" >> {LOG_FILE_PATH}'
    print(f"Debug log_mitigation_action: Ejecutando comando de log: {log_command}") # Debug log del comando
    try:
        log_execution_result = await run_remote_command(log_command)
        print(f"Debug log_mitigation_action: Resultado de comando de log: {log_execution_result}") # Debug resultado del comando de log
        if "Error" in log_execution_result or "Tiempo de espera agotado" in log_execution_result or "Error de conexión SSH" in log_execution_result:
             print(f"ERROR ejecutando comando de log remoto: {log_execution_result}")
             # Considerar si quieres notificar si falla el log
    except Exception as e:
        print(f"ERROR inesperado al ejecutar comando de log remoto: {e}")


# FUNCIÓN PARA FORMATTEAR EL MENSAJE DE AYUDA CATEGORIZADO
def format_help_message() -> str:
    """Formatea la descripción de comandos en categorías para MarkdownV2."""
    formatted_text = escape_markdown("🤖 Comandos disponibles:") + "\n\n"
    for category, commands in COMANDOS_DESCRIPCION_CATEGORIZED.items():
        formatted_text += f"*{escape_markdown(category)}:*\n\n"
        for command, description in commands:
            formatted_text += escape_markdown(command) + " \\- " + escape_markdown(description) + "\n"
        formatted_text += "\n"
    return formatted_text.strip()

# block_ip ahora usa run_remote_command, no necesita argumento 'conn'
async def block_ip(ip_address: str):
    """Bloquea una IP en el servidor remoto usando iptables y la registra (en memoria del bot)."""
    global blocked_ips

    if ip_address in blocked_ips:
        # No registramos aquí, ya que no es una nueva acción de bloqueo en iptables
        return f"La IP {ip_address} ya fue bloqueada previamente por este bot."
    command = f"sudo iptables -A INPUT -s {ip_address} -j DROP"
    description = f"Bloqueando todas las conexiones entrantes desde la IP {ip_address}"

    # Ejecutar el comando remoto
    result = await run_remote_command(command)

    # Verificar el resultado del comando remoto
    if not any(err_text in result for err_text in ["Error ejecutando el comando", "Error inesperado", "Tiempo de espera agotado", "Error de conexión SSH"]):
        # Si no hay errores conocidos en el resultado, asumir éxito en la ejecución del comando
        blocked_ips.add(ip_address)
        return f"{description}.\nComando: {command}\nResultado remoto: {result.strip()}"
    else:
        # Si hay un error conocido, devolver el mensaje de error de run_remote_command
        return f"Error al bloquear la IP {ip_address}: {result}"


# Helper para generar un identificador único para una alerta
def get_alert_identifier(alert):
    """Genera un identificador único para una alerta usando el hash de la línea raw."""
    if 'raw' in alert:
        return hashlib.sha256(alert['raw'].encode('utf-8')).hexdigest()
    # Fallback si 'raw' no está disponible, aunque debería estarlo
    fallback_id = f"{alert.get('timestamp')}-{alert.get('sid')}-{alert.get('src_ip')}-{alert.get('dest_ip')}-{alert.get('message')}"
    return hashlib.sha256(fallback_id.encode('utf-8')).hexdigest()


# Helper para leer entradas de log desde el servidor remoto desde un tiempo dado (usa run_remote_command)
async def get_log_entries_since(filepath: str, start_time_utc: datetime):
    """
    Lee entradas de log desde un archivo remoto desde un tiempo de inicio UTC dado.
    Asume que los timestamps en el log están en formato %Y-%m-%d %H:%M:%S UTC o ISO 8601 si es JSON.
    """
    # Usar la versión modificada de run_remote_command
    log_content = await run_remote_command(f"cat {filepath}")

    # Manejar posibles errores de run_remote_command
    if "Error de conexión SSH" in log_content or "Error ejecutando el comando" in log_content:
        print(f"ERROR al obtener entradas de log desde {filepath}: {log_content}")
        return []

    entries = []
    # Patrón para logs no JSON (el antiguo formato, lo mantenemos por compatibilidad al leer logs antiguos)
    legacy_log_pattern = re.compile(r'^(\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}) - (.*)$')

    for line in log_content.splitlines():
        try:
            # Intentar parsear como JSON (el nuevo formato)
            log_entry = json.loads(line)
            # Intentar obtener el timestamp del campo @timestamp (formato ISO 8601)
            if '@timestamp' in log_entry:
                log_timestamp_utc = datetime.fromisoformat(log_entry['@timestamp'])
                # Asegurarse de que sea un objeto datetime consciente de la zona horaria (UTC en este caso)
                if log_timestamp_utc.tzinfo is None:
                     log_timestamp_utc = log_timestamp_utc.replace(tzinfo=timezone.utc)

                if log_timestamp_utc >= start_time_utc:
                    # Para el resumen, podemos devolver la línea original o el objeto parseado.
                    # Devolver la línea original para mantener el formato de registro.
                    entries.append(line)
            else:
                 # Si no tiene @timestamp, intentar con el formato legado
                 match = legacy_log_pattern.match(line)
                 if match:
                    timestamp_str = match.group(1)
                    log_timestamp_naive = datetime.strptime(timestamp_str, '%Y-%m-%d %H:%M:%S')
                    log_timestamp_utc = pytz.utc.localize(log_timestamp_naive)

                    if log_timestamp_utc >= start_time_utc:
                        entries.append(line)
                 else:
                      print(f"Error: Línea de log sin formato JSON ni legado reconocido: {line}")


        except json.JSONDecodeError:
            # Si falla el parseo JSON, intentar con el formato legado
            match = legacy_log_pattern.match(line)
            if match:
                timestamp_str = match.group(1)
                try:
                    log_timestamp_naive = datetime.strptime(timestamp_str, '%Y-%m-%d %H:%M:%S')
                    log_timestamp_utc = pytz.utc.localize(log_timestamp_naive)

                    if log_timestamp_utc >= start_time_utc:
                         entries.append(line)
                except ValueError:
                    print(f"Error de formato de fecha en línea de log legado: {line}")
                    continue
            else:
                # Si no es ni JSON ni legado, ignorar o loguear
                # print(f"Línea ignorada por formato desconocido: {line}")
                pass
        except Exception as e:
             print(f"Error inesperado procesando línea de log '{line}': {e}")
             continue

    return entries


# Helper para obtener alertas de Suricata (usa run_remote_command)
async def get_recent_suricata_alerts():
    """Gets and parses the latest Suricata alerts, filtering temporary, blocked, and exception IPs."""
    result = await run_remote_command(COMANDOS['alertas'])

    if "Error de conexión SSH" in result or "Error ejecutando el comando" in result:
        print(f"ERROR al obtener alertas de Suricata: {result}")
        return []

    alerts = []
    # MADRID_TZ already defined globally

    for linea in result.strip().split('\n'):
        try:
            fecha_hora_match = re.match(r'(\d{2}/\d{2}/\d{4}-\d{2}:\d{2}:\d{2}(?:\.\d+)?)\s+', linea)
            if not fecha_hora_match:
                continue

            fecha_hora_completa_str = fecha_hora_match.group(1)
            naive_timestamp = None
            try:
                naive_timestamp = datetime.strptime(fecha_hora_completa_str, "%m/%d/%Y-%H:%M:%S.%f")
            except ValueError:
                try:
                    naive_timestamp = datetime.strptime(fecha_hora_completa_str, "%m/%d/%Y-%H:%M:%S")
                except ValueError:
                    print(f"Error de formato de fecha en alerta Suricata (get_recent): {fecha_hora_completa_str}")
                    continue

            # Localize to the server's timezone (assuming UTC)
            localized_timestamp_server = SERVER_TZ.localize(naive_timestamp)

            # Convert to Madrid time
            timestamp_madrid = localized_timestamp_server.astimezone(MADRID_TZ)

            # --- WORKAROUND: Subtract 2 hours as requested by the user ---
            timestamp_madrid_adjusted_for_display = timestamp_madrid - timedelta(hours=2)
            # --- END WORKAROUND ---

            fecha_hora_completa_madrid_str = timestamp_madrid_adjusted_for_display.strftime("%H:%M:%S")

            ip_match = re.search(r'(\d+\.\d+\.\d+\.\d+)(:\d+)?\s+->\s+(\d+\.\d+\.\d+\.\d+)(:\d+)?', linea)

            ip_origen = "N/A"
            ip_destino = "N/A"
            if ip_match:
                ip_origen = ip_match.group(1)
                ip_destino = ip_match.group(3)

            # --- FILTERING: Temporary IPs AND IPs blocked by the bot AND the server's own IP AND Exception IPs ---
            # <-- Modificado: Añadida condición para exception_ips
            if ip_origen.startswith("169.254.") or ip_destino.startswith("169.254.") or ip_origen in blocked_ips or ip_origen == REMOTE_HOST or ip_origen in exception_ips:
                continue

            alerta_match = re.search(r'\[\*\*\] (.*?) \[\*\*\]', linea)
            alerta = alerta_match.group(1).strip() if alerta_match else "Alerta sin formato [**]"

            # Extraer SID si está presente del formato [GeneratorID:SID:Revision]
            sid_match = re.search(r'\[\d+:(\d+):\d+\]', linea)
            sid = int(sid_match.group(1)) if sid_match else None

            alerts.append({'timestamp': fecha_hora_completa_madrid_str, 'src_ip': ip_origen, 'dest_ip': ip_destino, 'message': alerta, 'raw': linea, 'datetime_obj': timestamp_madrid, 'sid': sid})
        except Exception as e:
            print(f"Error parsing Suricata alert in get_recent_suricata_alerts: {e} - Line: {linea}")
            continue

    alerts.sort(key=lambda x: x['datetime_obj'], reverse=True)
    return alerts


# --- Funciones de inicialización ---
async def setup_remote_log_file(context: ContextTypes.DEFAULT_TYPE):
    """Asegura que el directorio y el archivo de log remoto existan y tengan permisos adecuados."""
    print(f"Verificando o creando archivo de log remoto: {LOG_FILE_PATH}")
    try:
        mkdir_cmd = f"sudo mkdir -p $(dirname {LOG_FILE_PATH})"
        print(f"Ejecutando en remoto: {mkdir_cmd}")
        mkdir_result = await run_remote_command(mkdir_cmd)
        if "Error" in mkdir_result or "Tiempo de espera agotado" in mkdir_result or "Error de conexión SSH" in mkdir_result:
             print(f"ERROR ejecutando mkdir remoto: {mkdir_result}")
        else:
             print("Directorio remoto verificado/creado.")

        touch_cmd = f"sudo touch {LOG_FILE_PATH}"
        print(f"Ejecutando en remoto: {touch_cmd}")
        touch_result = await run_remote_command(touch_cmd)
        if "Error" in touch_result or "Tiempo de espera agotado" in touch_result or "Error de conexión SSH" in touch_result:
             print(f"ERROR ejecutando touch remoto: {touch_result}")
        else:
             print("Archivo de log remoto verificado/creado.")

        # Opcional: dar ownership (si es necesario y sudoers lo permite)
        # chown_cmd = f"sudo chown {REMOTE_USER}:{REMOTE_USER} {LOG_FILE_PATH}"
        # print(f"Ejecutando en remoto: {chown_cmd}")
        # chown_result = await run_remote_command(chown_cmd)
        # if "Error" in chown_result: print(f"ERROR ejecutando chown remoto: {chown_result}")


        print("Configuración inicial del archivo de log remoto completada.")

        # Programar el trabajo periódico 'auto_mitigate'.
        context.job_queue.run_repeating(auto_mitigate_job, interval=60, first=0, name="auto_mitigate")
        print("Trabajo periódico 'auto_mitigate' programado.")

    except Exception as e:
        print(f"ERROR inesperado durante la configuración inicial del log remoto: {e}")
        print("El modo automático NO PODRÁ registrar acciones.")

# --- Trabajo periódico para el Modo Automático ---
async def auto_mitigate_job(context: ContextTypes.DEFAULT_TYPE):
    """Trabajo periódico para chequear alertas y mitigarlas automáticamente."""
    global is_auto_mode_active, processed_alerts_in_session, auto_mode_chat_id, blocked_ips

    if not is_auto_mode_active:
        return

    # print("Auto mode job: Chequeando alertas...") # Optional debug log

    try:
        alerts = await get_recent_suricata_alerts()

        ips_processed_in_this_job_run = set()

        # print(f"Auto mode job: Se obtuvieron {len(alerts)} alertas de get_recent_suricata_alerts.") # Mantén print temporal

        for alert in alerts:
            alert_id = get_alert_identifier(alert)
            source_ip = alert.get('src_ip')

            # print(f"  Procesando alerta ID: {alert_id}, SID: {alert.get('sid')}, IP: {source_ip}, Procesada antes (sesión): {alert_id in processed_alerts_in_session}, IP ya bloqueada (set global): {source_ip in blocked_ips}, IP procesada en esta ejecución: {source_ip in ips_processed_in_this_job_run}") # Mantén print temporal

            # --- Verificación temprana dentro del lote: Ignorar si esta IP ya la hemos manejado en esta ejecución ---
            if source_ip and source_ip in ips_processed_in_this_job_run:
                # print(f"  --> Saltando alerta de IP {source_ip}: Ya procesada (o encontrada como bloqueada) en esta ejecución del job.") # <-- Añade este print
                continue

            # Verificar si es un candidato para auto-bloqueo basado en SID y si NO ha sido procesada ANTES en ESTA SESIÓN del bot
            if alert.get('sid') in [1000001, 1000002, 1000003, 1000007, 1000008, 1000009] and alert_id not in processed_alerts_in_session: # Añadimos SID de DoS Web
                 # Extraer detalles de la alerta AQUÍ
                alert_message = alert['message']
                sid = alert.get('sid')

                print(f"  --> Procesando candidata para auto-bloqueo (potencialmente nueva): SID {sid}, IP {source_ip}")

                # Intentar bloquear la IP
                log_result = await block_ip(source_ip)

                print(f"  --> Resultado de block_ip para {source_ip}: {log_result}")

                # --- Añadir la IP al conjunto de IPs procesadas PARA BLOQUEO en *esta ejecución* del job ---
                if source_ip:
                    ips_processed_in_this_job_run.add(source_ip)
                # --- FIN Añadir a conjunto temporal ---

                # --- Verificar el resultado de block_ip y registrar/notificar ---
                if "Bloqueando todas las conexiones entrantes desde la IP" in log_result:
                    # El bloqueo fue NUEVO y exitoso en esta ejecución

                    print(f"  --> IP {source_ip} BLOQUEADA EXITOSAMENTE en esta ejecución.")

                    # Registrar el bloqueo exitoso en el log remoto en formato JSON
                    await log_mitigation_action({
                        'action_type': 'automatic_block_ip',
                        'source_ip': source_ip,
                        'alert_message': alert_message,
                        'sid': sid,
                        'result': log_result # Resultado de block_ip
                    })


                    # Enviar notificación SÓLO por el bloqueo NUEVO y exitoso
                    if auto_mode_chat_id:
                        notification_msg = (
                            escape_markdown("🛡️ *Modo Automático:* IP bloqueada.\n\n") +
                            escape_markdown("Alerta: `") + escape_markdown(f"{alert_message} [SID: {sid}]" if sid else alert_message) + escape_markdown("`\n") +
                            escape_markdown("IP de origen: `") + escape_markdown(source_ip) + escape_markdown("`\n\n") +
                            escape_markdown("Resultado del bloqueo: ") + f"```\n{escape_markdown(log_result).strip()}\n```"
                        )
                        try:
                            # print(f"  --> Enviando notificación de bloqueo EXITOSO para {source_ip} a chat {auto_mode_chat_id}")
                            await context.bot.send_message(chat_id=auto_mode_chat_id, text=notification_msg, parse_mode=ParseMode.MARKDOWN_V2)
                        except Exception as send_error:
                            print(f"  --> ERROR enviando notificación de bloqueo exitoso para {source_ip} a chat {auto_mode_chat_id}: {send_error}")

                elif "La IP" in log_result and "ya fue bloqueada previamente por este bot" in log_result:
                     # La IP ya estaba en nuestro set global 'blocked_ips'
                     print(f"  --> IP {source_ip} ya estaba bloqueada por el bot (detectado por block_ip).")
                     # No registrar en el archivo log (no es un nuevo bloqueo)
                     # No enviar notificación de bloqueo (no fue un bloqueo *nuevo*)

                else:
                    # Manejar otros posibles errores de block_ip (no 'ya bloqueada' y no éxito)
                    print(f"  --> block_ip devolvió un resultado inesperado o error para {source_ip}: {log_result}")
                    # Opcional: Podrías querer registrar estos errores o enviar una notificación de error específica.
                    # await log_mitigation_action({
                    #     'action_type': 'automatic_block_ip_failed',
                    #     'source_ip': source_ip,
                    #     'alert_message': alert_message,
                    #     'sid': sid,
                    #     'result': log_result # Resultado de block_ip
                    # })
                    # if auto_mode_chat_id:
                    #     error_notification = escape_markdown(f"❌ *Modo Automático: Error al bloquear IP*\n\nIP: `{escape_markdown(source_ip)}`\nAlerta: `{escape_markdown(alert_message)}`\nResultado: ```\n{escape_markdown(log_result).strip()}\n```")
                    #     await context.bot.send_message(chat_id=auto_mode_chat_id, text=error_notification, parse_mode=ParseMode.MARKDOWN_V2)


                # Marcar esta alerta como procesada *después* de intentar la acción para evitar duplicados en esta sesión del bot si se vuelve a leer
                processed_alerts_in_session.add(alert_id)

            # Else (la alerta no es candidata para auto-bloqueo por SID/sesión/IP ya procesada en este job run)
            # Este bloque se ejecuta para alertas que no cumplen los criterios de SID
            # o cuyo ID ya estaba en processed_alerts_in_session (alertas duplicadas ya manejadas en la sesión).
            # print(f"  --> Alerta {alert_id} de {source_ip}: No es candidata o ya procesada (sesión/este job run).") # Mantén print temporal si quieres ver estas


    except Exception as e:
        # Manejo de errores generales del job
        print(f"Error grave en auto_mitigate_job: {e}")
        error_notification = escape_markdown(f"❌ *Error grave en el Modo Automático:*\n") + escape_markdown(str(e))
        if auto_mode_chat_id:
            try:
                # print(f"  --> Enviando notificación de error a chat {auto_mode_chat_id}") # Mantén print temporal
                await context.bot.send_message(chat_id=auto_mode_chat_id, text=error_notification, parse_mode=ParseMode.MARKDOWN_V2)
            except Exception as send_error:
                 print(f"  --> ERROR enviando notificación de error a chat {auto_mode_chat_id}: {send_error}")


# --- Handlers para comandos ---

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /start command, showing the categorized help message."""
    await update.message.reply_text(
        format_help_message(),
        parse_mode=ParseMode.MARKDOWN_V2
    )

# Handler simple para cancelar un proceso
async def cancelar(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /cancelar command to cancel the current process."""
    await update.message.reply_text(
        escape_markdown("❌ *Comando de cancelación recibido.*"),
        parse_mode=ParseMode.MARKDOWN_V2
    )
    # Esto es solo un mensaje de confirmación.
    # La lógica real de cancelación para ConversationHandler está en el fallback.
    return ConversationHandler.END # Intentar finalizar si se usa como fallback


# Los siguientes handlers de comandos ahora usan run_remote_command sin pasar 'conn'
async def reiniciar(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /reiniciar command."""
    try:
        result = await run_remote_command(COMANDOS['reboot'])
        if "Error" in result or "Tiempo de espera agotado" in result or "Error de conexión SSH" in result:
            await update.message.reply_text(
                escape_markdown(f"❌ *Error al intentar reiniciar:*\n") + escape_markdown(result),
                parse_mode=ParseMode.MARKDOWN_V2
            )
        else:
            await update.message.reply_text(
                escape_markdown("🔄 *Reiniciando el servidor...*"),
                parse_mode=ParseMode.MARKDOWN_V2
            )
    except Exception as e:
        await update.message.reply_text(
            escape_markdown(f"❌ *Error inesperado al intentar reiniciar:*\n") + escape_markdown(str(e)),
            parse_mode=ParseMode.MARKDOWN_V2
        )

async def apagar(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /apagar command."""
    try:
        result = await run_remote_command(COMANDOS['poweroff'])
        if "Error" in result or "Tiempo de espera agotado" in result or "Error de conexión SSH" in result:
            await update.message.reply_text(
                escape_markdown(f"❌ *Error al intentar apagar:*\n") + escape_markdown(result),
                parse_mode=ParseMode.MARKDOWN_V2
            )
        else:
            await update.message.reply_text(
                escape_markdown("🛍 *Apagando el servidor...*"),
                parse_mode=ParseMode.MARKDOWN_V2
            )
    except Exception as e:
        await update.message.reply_text(
            escape_markdown(f"❌ *Error inesperado al intentar apagar:*\n") + escape_markdown(str(e)),
            parse_mode=ParseMode.MARKDOWN_V2
        )

async def exec_comando(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /exec command."""
    command = ' '.join(context.args)
    if not command:
        await update.message.reply_text(
            escape_markdown("❌ *Por favor, proporciona un comando para ejecutar.*"),
            parse_mode=ParseMode.MARKDOWN_V2
        )
        return
    try:
        result = await run_remote_command(command)
        result_escaped = escape_markdown(result)
        await update.message.reply_text(
            escape_markdown(f"📜 *Resultado del comando:* `{escape_markdown(command)}`\n") + f"```\n{result_escaped}\n```",
            parse_mode=ParseMode.MARKDOWN_V2
        )
    except Exception as e:
        await update.message.reply_text(
            escape_markdown(f"❌ *Error inesperado al ejecutar comando:*\n") + escape_markdown(str(e)),
            parse_mode=ParseMode.MARKDOWN_V2
        )

async def network_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /network_status command."""
    try:
        result = await run_remote_command(COMANDOS['network_status'])
        result_escaped = escape_markdown(result)
        await update.message.reply_text(
            escape_markdown(f"🌐 *Estado de la red:*\n") + f"```\n{result_escaped}\n```",
            parse_mode=ParseMode.MARKDOWN_V2
        )
    except Exception as e:
        await update.message.reply_text(
            escape_markdown(f"❌ *Error inesperado al obtener estado de red:*\n") + escape_markdown(str(e)),
            parse_mode=ParseMode.MARKDOWN_V2
        )

async def ping(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /ping command."""
    if context.args:
        ip = context.args[0]
        try:
            command = COMANDOS['ping'].format(ip=ip)
            result = await run_remote_command(command)
            result_escaped = escape_markdown(result)

            await update.message.reply_text(
                escape_markdown(f"🌐 *Resultado del ping a:* `{escape_markdown(ip)}`\n") + f"```\n{result_escaped}\n```",
                parse_mode=ParseMode.MARKDOWN_V2
            )
        except Exception as e:
            await update.message.reply_text(
                escape_markdown(f"❌ *Error inesperado al hacer ping:*\n") + escape_markdown(str(e)),
                parse_mode=ParseMode.MARKDOWN_V2
            )
    else:
        await update.message.reply_text(
            escape_markdown("❌ *Por favor, proporciona una IP o dominio para hacer ping.*"),
            parse_mode=ParseMode.MARKDOWN_V2
        )

async def accesos(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /accesos command."""
    try:
        result = await run_remote_command(COMANDOS['accesos'])

        if "Error de conexión SSH" in result or "Error ejecutando el comando" in result:
            await update.message.reply_text(
                escape_markdown(f"❌ *Error al obtener accesos SSH:*\n") + escape_markdown(result),
                parse_mode=ParseMode.MARKDOWN_V2
             )
            return
        accesos_limpios = []
        ahora_madrid = datetime.now(MADRID_TZ)

        for linea in result.strip().split('\n'):
            if "Accepted publickey" in linea:
                try:
                    fecha_hora_str = linea.split('+')[0]
                    naive_timestamp = None
                    try:
                        naive_timestamp = datetime.strptime(fecha_hora_str, "%Y-%m-%dT%H:%M:%S.%f")
                    except ValueError:
                        naive_timestamp = datetime.strptime(fecha_hora_str, "%Y-%m-%dT%H:%M:%S")

                    localized_timestamp_server = SERVER_TZ.localize(naive_timestamp)
                    timestamp_madrid = localized_timestamp_server.astimezone(MADRID_TZ)

                    # --- WORKAROUND: Subtract 2 hours as requested by the user ---
                    timestamp_madrid_adjusted_for_display = timestamp_madrid - timedelta(hours=2)
                    # --- END WORKAROUND ---

                    ip_match = re.search(r'from (\d+\.\d+\.\d+\.\d+)', linea)
                    ip = ip_match.group(1) if ip_match else "IP desconocida"

                    if ahora_madrid - timestamp_madrid <= timedelta(hours=24):
                        linea_escapada = escape_markdown(f"📅 {timestamp_madrid_adjusted_for_display.strftime('%Y-%m-%d %H:%M:%S %Z%z')} \\- 🌐 {ip}")
                        accesos_limpios.append(linea_escapada)

                except ValueError as e:
                    print(f"Error al procesar la fecha en la línea de acceso: {e} - Línea: {linea}")
                    continue
                except Exception as e:
                    print(f"Otro error al procesar la línea de acceso: {e} - Línea: {linea}")
                    continue

        texto = '\n'.join(accesos_limpios) if accesos_limpios else escape_markdown("No hay accesos en las últimas 24 horas.")
        await update.message.reply_text(
            escape_markdown("🔒 *Últimos accesos SSH:*\n") + texto,
            parse_mode=ParseMode.MARKDOWN_V2
        )
    except Exception as e:
         await update.message.reply_text(
            escape_markdown(f"❌ *Error inesperado al obtener accesos:*\n") + escape_markdown(str(e)),
            parse_mode=ParseMode.MARKDOWN_V2
        )

# mitigar ahora usa get_recent_suricata_alerts sin argumento 'conn'
async def mitigar(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /mitigar command, presenting alerts for blocking or other actions."""
    try:
        alerts_filtered = await get_recent_suricata_alerts()
        global recent_alerts
        recent_alerts[update.message.chat_id] = alerts_filtered

        blocked_ips_note = ""
        if blocked_ips:
            escaped_blocked_ips = [escape_markdown(ip) for ip in list(blocked_ips)[:5]]
            blocked_ips_list_str = ", ".join(escaped_blocked_ips)
            ellipsis_str = escape_markdown("...") if len(blocked_ips) > 5 else ""

            note_text = (
                escape_markdown("\n\n🚨 *Nota:* Las alertas de las siguientes IPs han sido filtradas por estar bloqueadas por el bot: ") +
                f"`{blocked_ips_list_str}{ellipsis_str}`" # Corregido: usar blocked_ips_list_str
            )
            blocked_ips_note = note_text

        # Nota sobre IPs de excepción
        exception_ips_note = ""
        if exception_ips:
            escaped_exception_ips = [escape_markdown(ip) for ip in list(exception_ips)[:5]]
            exception_ips_list_str = ", ".join(escaped_exception_ips)
            exception_ellipsis_str = escape_markdown("...") if len(exception_ips) > 5 else ""

            exception_note_text = (
                escape_markdown("\n🚨 *Nota:* Las alertas de las siguientes IPs han sido filtradas por estar en la lista de excepciones: ") +
                f"`{exception_ips_list_str}{exception_ellipsis_str}`"
            )
            exception_ips_note = exception_note_text


        if not alerts_filtered:
            msg = escape_markdown("🔍 *No hay alertas recientes para gestionar (excluyendo IPs temporales, ya bloqueadas por el bot, la propia IP del servidor, o en la lista de excepciones).* \n\n")
            msg += blocked_ips_note
            msg += exception_ips_note # Añadir nota de excepciones
            await update.message.reply_text(msg, parse_mode=ParseMode.MARKDOWN_V2)
            return

        keyboard_buttons = []
        alertas_agrupadas = defaultdict(list)
        alerta_msg_to_index = {}

        for i, alert in enumerate(alerts_filtered):
            clave_alerta = alert['message']
            alertas_agrupadas[clave_alerta].append(alert['src_ip'])
            if clave_alerta not in alerta_msg_to_index:
                alerta_msg_to_index[clave_alerta] = i

        for alerta_msg, ips_list in alertas_agrupadas.items():
            count = len(ips_list)
            first_occurrence_index = alerta_msg_to_index[alerta_msg]
            repeticion = f" (x{count})" if count > 1 else ""
            button_text = f"{alerta_msg}{repeticion}"
            if len(button_text) > 64:
                button_text = button_text[:61] + "..."

            keyboard_buttons.append([InlineKeyboardButton(escape_markdown(button_text), callback_data=f"select_alert_{first_occurrence_index}")])

        reply_markup = InlineKeyboardMarkup(keyboard_buttons)
        msg = escape_markdown("⚠️ *Elige la alerta que deseas gestionar:*\n_(Se mostrará la IP de origen asociada a la primera aparición de esta alerta)_")
        msg += blocked_ips_note
        msg += exception_ips_note # Añadir nota de excepciones

        await update.message.reply_text(
            msg,
            parse_mode=ParseMode.MARKDOWN_V2,
            reply_markup=reply_markup
        )
    except Exception as e:
        await update.message.reply_text(
            escape_markdown(f"❌ *Error al obtener alertas para gestionar:*\n") + escape_markdown(str(e)),
            parse_mode=ParseMode.MARKDOWN_V2
        )

# --- NUEVA FUNCIÓN: handle_mitigation_choice ---
async def handle_mitigation_choice(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the user's selection of an alert for mitigation."""
    query = update.callback_query
    await query.answer()

    try:
        # The callback_data is in the format "select_alert_<index>"
        alert_index = int(query.data.split('_')[2])
    except (IndexError, ValueError):
        await query.edit_message_text(escape_markdown("❌ *Error al procesar la selección de alerta (datos inválidos).*"), parse_mode=ParseMode.MARKDOWN_V2)
        return

    chat_id = query.message.chat_id
    alerts_filtered = recent_alerts.get(chat_id)

    if alerts_filtered and 0 <= alert_index < len(alerts_filtered):
        selected_alert = alerts_filtered[alert_index]
        source_ip = selected_alert.get('src_ip', 'N/A')
        alert_message = selected_alert.get('message', 'N/A')
        sid = selected_alert.get('sid')

        # Store the selected alert information in user_data for the next step
        context.user_data['selected_alert'] = selected_alert

        # Present mitigation options
        keyboard = [
            [InlineKeyboardButton(escape_markdown("🚫 Bloquear IP"), callback_data=f"confirm_action_blockip_{alert_index}")],
            [InlineKeyboardButton(escape_markdown("🔬 Ejecutar Script Web"), callback_data=f"confirm_action_runwebshellscript_{alert_index}")],
            # [InlineKeyboardButton(escape_markdown("🔍 Investigar Conexiones"), callback_data=f"confirm_action_investigateconnections_{alert_index})], # Optional: if implemented
            [InlineKeyboardButton(escape_markdown("👁️ Reconocer Alerta"), callback_data=f"confirm_action_acknowledge_{alert_index}")],
            [InlineKeyboardButton(escape_markdown("❌ Cancelar"), callback_data="cancel_action")]
        ]
        reply_markup = InlineKeyboardMarkup(keyboard)

        message_text = (
            escape_markdown("⚠️ *Alerta seleccionada:*\n\n") +
            escape_markdown("Mensaje: `") + escape_markdown(f"{alert_message} [SID: {sid}]" if sid else alert_message) + escape_markdown("`\n") +
            escape_markdown("IP de origen: `") + escape_markdown(source_ip) + escape_markdown("`\n\n") +
            escape_markdown("Elige una acción de mitigación:")
        )

        await query.edit_message_text(
            message_text,
            parse_mode=ParseMode.MARKDOWN_V2,
            reply_markup=reply_markup
        )
    else:
        await query.edit_message_text(
            escape_markdown("❌ *La alerta seleccionada no es válida para gestionar o la lista ha expirado.*"),
            parse_mode=ParseMode.MARKDOWN_V2
        )


# Handlers para Callback Queries (Mitigación interactiva) - Usan block_ip/run_remote_command sin 'conn'
async def handle_confirmed_action(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the confirmation of a mitigation action."""
    query = update.callback_query
    await query.answer()

    try:
        parts = query.data.split('_')
        if len(parts) < 4:
             await query.edit_message_text(escape_markdown("❌ *Error al procesar la acción de mitigación (formato inválido).*"), parse_mode=ParseMode.MARKDOWN_V2)
             return
        action_type = parts[2]
        alert_index = int(parts[3])
    except (IndexError, ValueError):
        await query.edit_message_text(escape_markdown("❌ *Error al procesar la acción de mitigación (datos inválidos).*"), parse_mode=ParseMode.MARKDOWN_V2)
        return

    chat_id = query.message.chat_id
    # Retrieve the selected alert from user_data instead of recent_alerts
    selected_alert = context.user_data.pop('selected_alert', None) # Remove it after use

    # Clean up the stored alerts for this chat_id immediately
    if chat_id in recent_alerts:
         del recent_alerts[chat_id]

    if selected_alert: # Check if selected_alert was successfully retrieved
        source_ip = selected_alert.get('src_ip', 'N/A') # Usar .get() para evitar KeyError si el campo no existe
        alert_message = selected_alert.get('message', 'N/A')
        sid = selected_alert.get('sid')
        action_description = ""
        command_to_run = None # Variable para almacenar el comando ejecutado

        message_text_header = escape_markdown("⚙️ *Resultado de la acción:*\n\n")
        action_result_text = ""
        log_action_type = f"manual_{action_type}" # Tipo de acción para el log
        user = query.from_user.username or str(query.from_user.id) # Usuario que inició la acción

        try:
            if action_type == "blockip":
                action_description = "Bloqueo de IP"
                if source_ip in blocked_ips:
                   await query.edit_message_text(
                       escape_markdown(f"ℹ️ *La IP* `{escape_markdown(source_ip)}` *ya fue bloqueada previamente por este bot.*"),
                       parse_mode=ParseMode.MARKDOWN_V2
                   )
                   # No registrar en el log remoto si ya estaba bloqueada por el bot
                   return

                action_result_text = await block_ip(source_ip)

                # Registrar en el log remoto después de intentar el bloqueo
                await log_mitigation_action({
                    'action_type': log_action_type,
                    'source_ip': source_ip,
                    'alert_message': alert_message,
                    'sid': sid,
                    'user': user,
                    'result': action_result_text # Resultado de block_ip
                    # block_ip ya incluye el comando si tiene éxito, no lo añadimos dos veces aquí
                })

                if "Bloqueando todas las conexiones entrantes desde la IP" in action_result_text:
                    message_text_header = escape_markdown("✅ *IP bloqueada:* `{escape_markdown(source_ip)}`\n\n") # Change header on success

                # Registrar en el log remoto
                # Esta parte de registrar se repite, lo ideal sería registrar una vez al final,
                # pero manteniendo la estructura original, se deja así por ahora.
                # await log_mitigation_action({
                #     'action_type': log_action_type,
                #     'source_ip': source_ip,
                #     'alert_message': alert_message,
                #     'sid': sid,
                #     'user': user,
                #     'command': command_to_run, # command_to_run es None para blockip, block_ip lo registra internamente si tiene éxito
                #     'result': action_result_text
                # })


            elif action_type == "runwebshellscript":
                action_description = "Ejecutar Script de Investigación Web"
                command_to_run = COMANDOS.get('run_web_script', '').format(ip=source_ip) # Usar .get para seguridad
                if not command_to_run:
                     action_result_text = escape_markdown("Comando de script web no configurado.")
                else:
                     action_result_text = await run_remote_command(command_to_run)
                message_text_header = escape_markdown("🔬 *Resultado del script de investigación para* `{escape_markdown(source_ip)}`*:\n\n")

                # Registrar en el log remoto
                await log_mitigation_action({
                    'action_type': log_action_type,
                    'source_ip': source_ip,
                    'alert_message': alert_message,
                    'sid': sid,
                    'user': user,
                    'command': command_to_run,
                    'result': action_result_text
                })


            elif action_type == "acknowledge":
                 action_description = "Reconocimiento de Alerta"
                 action_result_text = escape_markdown("La alerta ha sido reconocida manualmente.")
                 message_text_header = escape_markdown("ℹ️ *Alerta reconocida:*\n\n")

                 # Registrar en el log remoto
                 await log_mitigation_action({
                    'action_type': log_action_type,
                    'source_ip': source_ip,
                    'alert_message': alert_message,
                    'sid': sid,
                    'user': user,
                    'result': "Alert acknowledged via bot"
                 })

            # Añadir manejo para 'investigateconnections' si es necesario implementarlo.
            # elif action_type == "investigateconnections":
            #     action_description = "Investigar Conexiones"
            #     # Implementar lógica para investigar conexiones (ej. 'ss -tn src <ip>')
            #     # action_result_text = await run_remote_command(...)
            #     message_text_header = escape_markdown(f"🔍 *Resultado de la investigación para* `{escape_markdown(source_ip)}`*:\n\n")
            #     await log_mitigation_action({
            #         'action_type': log_action_type,
            #         'source_ip': source_ip,
            #         'alert_message': alert_message,
            #         'sid': sid,
            #         'user': user,
            #         'command': 'ss -tn src <ip>', # O el comando real
            #         'result': action_result_text
            #     })


            else:
                action_description = "Acción Desconocida"
                action_result_text = escape_markdown("Tipo de acción de mitigación desconocido.")
                message_text_header = escape_markdown("❌ *Error:*\n\n")
                # Opcional: Registrar error de acción desconocida


            message_to_send = (
                message_text_header +
                escape_markdown("Alerta: `") + escape_markdown(f"{alert_message} [SID: {sid}]" if sid else alert_message) + escape_markdown("`\n") +
                escape_markdown("IP de origen: `") + escape_markdown(source_ip) + escape_markdown("`\n\n")
            )

            # Add command result in a code block if there is any significant output or handled error message
            if action_result_text and not action_result_text.startswith(escape_markdown("La alerta ha sido reconocida manualmente")):
                 # Si contiene un mensaje de error conocido de run_remote_command, mostrarlo.
                 if "Error ejecutando el comando" in action_result_text or "Error inesperado" in action_result_text or "Tiempo de espera agotado" in action_result_text or "Error de conexión SSH" in action_result_text:
                     message_to_send += f"```\n{escape_markdown(action_result_text).strip()}\n```"
                 elif action_type == "blockip" and "Bloqueando todas las conexiones" in action_result_text:
                      # Mensaje de éxito de block_ip - añadir escapado sin bloque de código
                      message_to_send += escape_markdown(action_result_text.strip())
                 else:
                    # Cualquier otro resultado significativo (ej. salida de ss) en bloque de código
                    message_to_send += f"```\n{escape_markdown(action_result_text).strip()}\n```"
            elif action_result_text: # Mostrar mensajes de reconocimiento simples directamente (ya escapados)
                 message_to_send += escape_markdown(action_result_text.strip())


        except Exception as e:
             action_description = action_description or "Error de Conexión/Ejecución"
             message_to_send = (
                 escape_markdown(f"❌ *Error inesperado durante la acción de {action_description}:*\n\n") +
                 escape_markdown("Alerta: `") + escape_markdown(f"{alert_message} [SID: {sid}]" if sid else alert_message) + escape_markdown("`\n") +
                 escape_markdown("IP de origen: `") + escape_markdown(source_ip) + escape_markdown("`\n\n") +
                 escape_markdown(f"Detalles del error: {e}")
            )
             # Opcional: Registrar error inesperado en el log
             # await log_mitigation_action({
             #     'action_type': f"{log_action_type}_unexpected_error",
             #     'source_ip': source_ip,
             #     'alert_message': alert_message,
             #     'sid': sid,
             #     'user': user,
             #     'command': command_to_run,
             #     'result': f"Unexpected error: {e}"
             # })


        await query.edit_message_text(
            message_to_send,
            parse_mode=ParseMode.MARKDOWN_V2
        )

    else:
        await query.edit_message_text(
            escape_markdown("❌ *La alerta seleccionada no es válida para gestionar o la lista ha expirado.*"),
            parse_mode=ParseMode.MARKDOWN_V2
        )


async def handle_cancel_action(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles cancelling the mitigation action and logs it."""
    query = update.callback_query
    await query.answer()

    chat_id = query.message.chat_id
    # Intentar obtener el índice de la alerta del callback_data (si es posible)
    alert_index = None
    try:
        # Pattern: cancel_action_<index>
        # Intentar extraer el índice si el callback_data lo incluye, aunque para 'cancel_action' puro no lo tendrá
        parts = query.data.split('_')
        if len(parts) > 2 and parts[1] == 'action': # Asegurarse de que es una cancelación de acción de mitigación
             alert_index = int(parts[2]) # El índice estaría en la tercera posición si el formato fuera cancel_action_<index>
    except (IndexError, ValueError):
         pass # Ignorar si no se puede parsear el índice, no es crítico para la cancelación

    alerts_filtered = recent_alerts.get(chat_id)
    selected_alert_info = None # Para almacenar la información de la alerta si se encuentra

    # Obtener la información de la alerta antes de limpiarla, solo si el índice es válido y se encontró
    if alerts_filtered and alert_index is not None and 0 <= alert_index < len(alerts_filtered):
         selected_alert_info = alerts_filtered[alert_index]

    # Limpiar las alertas almacenadas para este chat_id
    if chat_id in recent_alerts:
         del recent_alerts[chat_id]

    # Registrar la acción de cancelación SOLO si pudimos obtener la información de la alerta
    if selected_alert_info:
        source_ip = selected_alert_info.get('src_ip', 'N/A')
        alert_message = selected_alert_info.get('message', 'N/A')
        sid = selected_alert_info.get('sid')
        user = query.from_user.username or str(query.from_user.id)

        await log_mitigation_action({
            'action_type': 'manual_cancelled', # Un nuevo tipo para las cancelaciones
            'source_ip': source_ip,
            'alert_message': alert_message,
            'sid': sid,
            'user': user,
            'result': 'Mitigation action cancelled by user'
        })

    await query.edit_message_text(escape_markdown("❌ *Acción de mitigación cancelada.*"), parse_mode=ParseMode.MARKDOWN_V2)

# alertas ahora usa get_recent_suricata_alerts sin argumento 'conn'
async def alertas(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /alertas command, showing filtered recent alerts."""
    try:
        alerts_filtered = await get_recent_suricata_alerts()

        blocked_ips_note = ""
        if blocked_ips:
            escaped_blocked_ips = [escape_markdown(ip) for ip in list(blocked_ips)[:5]]
            blocked_ips_list_str = ", ".join(escaped_blocked_ips)
            ellipsis_str = escape_markdown("...") if len(blocked_ips) > 5 else ""

            note_text = (
                escape_markdown("\n\n🚨 *Nota:* Las alertas de las siguientes IPs han sido filtradas por estar bloqueadas por el bot: ") +
                f"`{blocked_ips_list_str}{ellipsis_str}`" # Corregido: usar blocked_ips_list_str
            )
            blocked_ips_note = note_text

        # Nota sobre IPs de excepción
        exception_ips_note = ""
        if exception_ips:
            escaped_exception_ips = [escape_markdown(ip) for ip in list(exception_ips)[:5]]
            exception_ips_list_str = ", ".join(escaped_exception_ips)
            exception_ellipsis_str = escape_markdown("...") if len(exception_ips) > 5 else ""

            exception_note_text = (
                escape_markdown("\n🚨 *Nota:* Las alertas de las siguientes IPs han sido filtradas por estar en la lista de excepciones: ") +
                f"`{exception_ips_list_str}{exception_ellipsis_str}`"
            )
            exception_ips_note = exception_note_text


        if not alerts_filtered:
            msg = escape_markdown("🔍 *No hay alertas recientes (excluyendo IPs temporales, ya bloqueadas por el bot, la propia IP del servidor, o en la lista de excepciones) en el log de Suricata (última hora).*")
            msg += blocked_ips_note
            msg += exception_ips_note # Añadir nota de excepciones
            await update.message.reply_text(msg, parse_mode=ParseMode.MARKDOWN_V2)
            return

        # Use defaultdict to group by message type
        alertas_agrupadas_info = defaultdict(lambda: {'count': 0, 'first_ip': 'N/A', 'first_dest_ip': 'N/A', 'first_time_obj': None, 'sid': None})

        for alert in alerts_filtered:
            clave = alert['message']
            alertas_agrupadas_info[clave]['count'] += 1
            if alertas_agrupadas_info[clave]['count'] == 1:
                alertas_agrupadas_info[clave]['first_ip'] = alert['src_ip']
                alertas_agrupadas_info[clave]['first_dest_ip'] = alert['dest_ip']
                alertas_agrupadas_info[clave]['first_time_obj'] = alert['datetime_obj']
                alertas_agrupadas_info[clave]['sid'] = alert.get('sid')

        sorted_keys = sorted(
            alertas_agrupadas_info.keys(),
            key=lambda clave: alertas_agrupadas_info[clave]['first_time_obj'],
            reverse=True
        )

        alertas_formateadas = []
        for clave in sorted_keys:
            info = alertas_agrupadas_info[clave]
            count = info['count']
            first_ip = info['first_ip']
            first_dest_ip = info['first_dest_ip']
            sid = info['sid']
            first_time_formatted_obj = info['first_time_obj']

            # --- WORKAROUND: Subtract 2 hours as requested by the user ---
            first_time_formatted_obj_adjusted_for_display = first_time_formatted_obj - timedelta(hours=2)
            # --- END WORKAROUND ---

            first_time_formatted_str = first_time_formatted_obj_adjusted_for_display.strftime("%H:%M:%S")

            repeticion_str = f" (x{count})" if count > 1 else ""
            ips_str = f"🔴 {first_ip} → 🟢 {first_dest_ip}"
            sid_str = f" [SID: {sid}]" if sid else ""

            time_part = escape_markdown(f"📅 {first_time_formatted_str}{repeticion_str}")
            ips_part = escape_markdown(f"{ips_str}")
            alerta_part = escape_markdown(clave) + escape_markdown(sid_str)

            linea_formateada = f"{time_part} \\- {ips_part}\n⚠️ {alerta_part}"

            alertas_formateadas.append(linea_formateada)

        respuesta = escape_markdown("🚨 *Alertas de Suricata (última hora - Madrid):*\n\n") + "\n".join(alertas_formateadas)
        respuesta += blocked_ips_note
        respuesta += exception_ips_note # Añadir nota de excepciones

        await update.message.reply_text(
            respuesta,
            parse_mode=ParseMode.MARKDOWN_V2
        )
    except Exception as e:
         await update.message.reply_text(
            escape_markdown(f"❌ *Error inesperado al obtener alertas de Suricata:*\n") + escape_markdown(str(e)),
            parse_mode=ParseMode.MARKDOWN_V2
        )

# Los siguientes handlers de comandos ahora usan run_remote_command sin pasar 'conn'
async def memory_usage(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /memory_usage command."""
    try:
        result = await run_remote_command(COMANDOS['memory_usage'])
        result_escaped = escape_markdown(result)
        await update.message.reply_text(
            escape_markdown(f"🧠 *Uso de memoria:*\n") + f"```\n{result_escaped}\n```",
            parse_mode=ParseMode.MARKDOWN_V2
        )
    except Exception as e:
         await update.message.reply_text(
            escape_markdown(f"❌ *Error inesperado al obtener uso de memoria:*\n") + escape_markdown(str(e)),
            parse_mode=ParseMode.MARKDOWN_V2
        )

async def disk_usage(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /disk_usage command."""
    try:
        result = await run_remote_command(COMANDOS['disk_usage'])
        result_escaped = escape_markdown(result)
        await update.message.reply_text(
            escape_markdown(f"📝 *Uso de disco:*\n") + f"```\n{result_escaped}\n```",
            parse_mode=ParseMode.MARKDOWN_V2
        )
    except Exception as e:
         await update.message.reply_text(
            escape_markdown(f"❌ *Error inesperado al obtener uso de disco:*\n") + escape_markdown(str(e)),
            parse_mode=ParseMode.MARKDOWN_V2
        )

async def uptime(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /uptime command."""
    try:
        result = await run_remote_command(COMANDOS['uptime'])
        await update.message.reply_text(
            escape_markdown(f"🕒 *Tiempo de actividad:* ") + escape_markdown(result.strip()),
            parse_mode=ParseMode.MARKDOWN_V2
        )
    except Exception as e:
         await update.message.reply_text(
            escape_markdown(f"❌ *Error inesperado al obtener tiempo de actividad:*\n") + escape_markdown(str(e)),
            parse_mode=ParseMode.MARKDOWN_V2
        )

# check command does NOT use asyncssh, it uses socket, so it remains the same
async def check(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /check command to verify SSH connectivity."""
    try:
        conn_socket = socket.create_connection((REMOTE_HOST, 22), timeout=3)
        conn_socket.close()
        await update.message.reply_text(
            escape_markdown("✅ *El servidor está encendido y responde en el puerto SSH.*"),
            parse_mode=ParseMode.MARKDOWN_V2
        )
    except (socket.timeout, ConnectionRefusedError):
        await update.message.reply_text(
            escape_markdown("❌ *El servidor no está accesible o no responde en el puerto SSH.*"),
            parse_mode=ParseMode.MARKDOWN_V2
        )
    except Exception as e:
         print(f"Error inesperado en check: {e}")
         await update.message.reply_text(
            escape_markdown("❌ *Ocurrió un error inesperado al verificar el estado del servidor:*\n") + escape_markdown(str(e)),
            parse_mode=ParseMode.MARKDOWN_V2
        )


# Handler para el Modo Automático - Usa la conexión persistente a través de las funciones llamadas
async def modo_automatico(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /modo_automatico command to toggle automatic mitigation."""
    status_text = escape_markdown(f"⚙️ *Modo Automático:* {'Activado' if is_auto_mode_active else 'Desactivado'}")
    keyboard = [[
        InlineKeyboardButton(escape_markdown("❌ Desactivar"), callback_data="auto_mode_deactivate") if is_auto_mode_active else
        InlineKeyboardButton(escape_markdown("✅ Activar"), callback_data="auto_mode_activate")
    ]]
    reply_markup = InlineKeyboardMarkup(keyboard)

    await update.message.reply_text(status_text, reply_markup=reply_markup, parse_mode=ParseMode.MARKDOWN_V2)

# handle_auto_mode_callback - Usa get_log_entries_since sin 'conn'
async def handle_auto_mode_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles callbacks for /modo_automatico buttons."""
    query = update.callback_query
    await query.answer()

    global is_auto_mode_active, auto_mode_start_time, processed_alerts_in_session, auto_mode_chat_id

    try:
        action = query.data.split('_')[2]
        message_text = ""

        if action == "activate":
            if not is_auto_mode_active:
                is_auto_mode_active = True
                auto_mode_start_time = datetime.now(timezone.utc) # Usar datetime consciente de zona horaria
                processed_alerts_in_session.clear()
                auto_mode_chat_id = query.message.chat_id
                message_text = escape_markdown("✅ *Modo Automático Activado.* Se bloquearán IPs automáticamente para las alertas de tipo [SSH], [DoS] (IP), [Scan] (TCP), y DoS Web. Se registrarán las acciones en el servidor.")
                await query.edit_message_text(message_text, parse_mode=ParseMode.MARKDOWN_V2)

            else:
                message_text = escape_markdown("ℹ️ *El Modo Automático ya está activado.*")
                await query.edit_message_text(message_text, parse_mode=ParseMode.MARKDOWN_V2)


        elif action == "deactivate":
            if is_auto_mode_active:
                is_auto_mode_active = False
                auto_mode_end_time = datetime.now(timezone.utc) # Usar datetime consciente de zona horaria
                auto_mode_duration = auto_mode_end_time - (auto_mode_start_time if auto_mode_start_time else auto_mode_end_time)


                # --- Generar Resumen ---
                summary_text = escape_markdown("✅ *Modo Automático Desactivado.*\n\n")
                start_time_madrid_str = escape_markdown(auto_mode_start_time.astimezone(MADRID_TZ).strftime('%Y-%m-%d %H:%M:%S %Z%z')) if auto_mode_start_time else escape_markdown("desconocido")
                end_time_madrid_str = escape_markdown(auto_mode_end_time.astimezone(MADRID_TZ).strftime('%Y-%m-%d %H:%M:%S %Z%z'))
                summary_text += escape_markdown(f"Periodo activo (Madrid): Desde ") + start_time_madrid_str + escape_markdown(" hasta ") + end_time_madrid_str + "\n"
                summary_text += escape_markdown(f"Duración: ") + escape_markdown(str(auto_mode_duration).split('.')[0]) + "\n"
                summary_text += escape_markdown(f"Log de acciones en el servidor: `{escape_markdown(LOG_FILE_PATH)}`\n\n")

                # Intenta leer el log y contar/listar entradas durante la sesión
                try:
                     log_entries = await get_log_entries_since(LOG_FILE_PATH, auto_mode_start_time)
                     blocked_count = len(log_entries)
                     summary_text += escape_markdown(f"Total de acciones automáticas registradas en este periodo: ") + escape_markdown(str(blocked_count)) + "\n\n"

                     if blocked_count > 0:
                         summary_text += escape_markdown("Últimas 5 acciones (formato raw del log):\n```\n")
                         for entry in log_entries[-5:]:
                              summary_text += escape_markdown(entry.strip()) + "\n"
                         summary_text += "```"
                     else:
                         summary_text += escape_markdown("No se registraron acciones automáticas en este periodo.")


                except Exception as e:
                     summary_text += escape_markdown(f"❌ *Error al leer el log de acciones automáticas:*\n") + escape_markdown(str(e))

                await query.edit_message_text(summary_text, parse_mode=ParseMode.MARKDOWN_V2)

                # Reset state variables AFTER sending summary
                processed_alerts_in_session.clear()
                auto_mode_start_time = None
                auto_mode_chat_id = None

            else:
                message_text = escape_markdown("ℹ️ *El Modo Automático ya está desactivado.*")
                await query.edit_message_text(message_text, parse_mode=ParseMode.MARKDOWN_V2)

    except Exception as e:
        print(f"Error en handle_auto_mode_callback: {e}")
        await query.edit_message_text(escape_markdown(f"❌ *Ocurrió un error al cambiar el estado del modo automático:*\n") + escape_markdown(str(e)), parse_mode=ParseMode.MARKDOWN_V2)


# --- Nuevo Handler para Desbloquear IP ---
async def unblock_ip_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /desbloquear command to unblock an IP."""
    global blocked_ips

    if not context.args:
        await update.message.reply_text(
            escape_markdown("❌ *Por favor, proporciona la IP que deseas desbloquear.*"),
            parse_mode=ParseMode.MARKDOWN_V2
        )
        return

    ip_to_unblock = context.args[0]

    if not re.match(r'^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$', ip_to_unblock):
         await update.message.reply_text(
            escape_markdown(f"❌ *Formato de IP inválido:* `{escape_markdown(ip_to_unblock)}`"),
            parse_mode=ParseMode.MARKDOWN_V2
        )
         return

    is_in_blocked_set = ip_to_unblock in blocked_ips

    # Intentar eliminar la regla de iptables de todas formas
    try:
        command = COMANDOS.get('unblock_ip_cmd', '').format(ip=ip_to_unblock) # Usar .get para seguridad
        if not command:
             await update.message.reply_text(escape_markdown("❌ *Comando para desbloquear IP no configurado.*"), parse_mode=ParseMode.MARKDOWN_V2)
             return

        print(f"Intentando desbloquear IP: {ip_to_unblock} usando comando: {command}")
        result = await run_remote_command(command)

        user = update.message.from_user.username or str(update.message.from_user.id)

        # Verificar el resultado de run_remote_command.
        if "Error ejecutando el comando" in result or "Error inesperado" in result or "Tiempo de espera agotado" in result or "Error de conexión SSH" in result:
             error_message = result
             # Si el error es que la regla no existía, manejarlo específicamente.
             if "No chain/target/match by that name" in result or "no matching rule" in result:
                  error_message = escape_markdown(f"⚠️ *No se encontró una regla de bloqueo para la IP* `{escape_markdown(ip_to_unblock)}` *en iptables.*")
                  # Si no se encontró en iptables, asegurar que tampoco esté en nuestro set por si acaso.
                  if ip_to_unblock in blocked_ips:
                      blocked_ips.remove(ip_to_unblock)
                      error_message += escape_markdown("\nSe ha eliminado de la lista interna del bot.")
                  # Registrar en el log remoto el intento fallido (regla no encontrada)
                  await log_mitigation_action({
                        'action_type': 'manual_unblock_ip_rule_not_found',
                        'source_ip': ip_to_unblock,
                        'user': user,
                        'command': command,
                        'result': result
                  })
             else:
                  # Otros errores de ejecución remota no relacionados con regla no encontrada.
                  error_message = escape_markdown(f"❌ *Error al intentar eliminar la regla de iptables para* `{escape_markdown(ip_to_unblock)}`*:\n") + escape_markdown(result)
                  # Registrar en el log remoto el intento fallido (otro error)
                  await log_mitigation_action({
                        'action_type': 'manual_unblock_ip_failed_remote_command',
                        'source_ip': ip_to_unblock,
                        'user': user,
                        'command': command,
                        'result': result
                  })

             await update.message.reply_text(error_message, parse_mode=ParseMode.MARKDOWN_V2)

        else:
            # Si run_remote_command no devolvió un mensaje de error conocido, asumimos que el comando iptables -D tuvo éxito.
            if ip_to_unblock in blocked_ips:
                blocked_ips.remove(ip_to_unblock)
                print(f"IP {ip_to_unblock} eliminada del set blocked_ips.")

            # Registrar en el log remoto el desbloqueo exitoso
            await log_mitigation_action({
                'action_type': 'manual_unblock_ip_successful',
                'source_ip': ip_to_unblock,
                'user': user,
                'command': command,
                'result': "IP successfully unblocked"
            })

            await update.message.reply_text(
                escape_markdown(f"🔓 *La IP* `{escape_markdown(ip_to_unblock)}` *ha sido desbloqueada (regla de iptables eliminada y eliminada de la lista interna del bot).*"),
                parse_mode=ParseMode.MARKDOWN_V2
            )

    except Exception as e:
        user = update.message.from_user.username or str(update.message.from_user.id)
        # Capturar otros errores inesperados durante el handler.
        await update.message.reply_text(
            escape_markdown(f"❌ *Ocurrió un error inesperado al intentar desbloquear la IP* `{escape_markdown(ip_to_unblock)}`*:\n") + escape_markdown(str(e)),
            parse_mode=ParseMode.MARKDOWN_V2
        )
        # Opcional: Registrar error inesperado
        # await log_mitigation_action({
        #     'action_type': 'manual_unblock_ip_unexpected_error',
        #     'source_ip': ip_to_unblock,
        #     'user': user,
        #     'result': f"Unexpected error: {e}"
        # })

# --- NUEVOS HANDLERS PARA EL COMANDO /excepciones ---
async def excepciones(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    """Handles the /excepciones command, shows the list and asks to add a new one."""
    chat_id = update.message.chat_id
    user = update.message.from_user

    list_of_exceptions = list(exception_ips)

    if not list_of_exceptions:
        # Escape the entire message if there are no IPs, as it contains no backticks around IPs
        message_text = escape_markdown("Estas son las excepciones de IPs para las alertas:\n\n_No hay IPs de excepción configuradas actualmente._")
    else:
        # Build the message piece by piece, escaping non-IP parts
        message_text = escape_markdown("Estas son las excepciones de IPs para las alertas:\n\n")
        for ip in list_of_exceptions:
            # Escape the IP specifically for display within backticks (escape dots)
            escaped_ip_content = ip.replace('.', '\.')
            # Build the line: escaped list marker, literal backtick, escaped IP content, literal backtick, escaped newline
            # Don't escape the backticks here, as we won't escape the whole message_text at the end.
            line = escape_markdown("- ") + "`" + escaped_ip_content + "`" + escape_markdown("\n")
            message_text += line


    keyboard = [
        [InlineKeyboardButton(escape_markdown("➕ Añadir nueva IP"), callback_data="add_exception_ip")],
        [InlineKeyboardButton(escape_markdown("❌ Cancelar"), callback_data="cancel_exception_flow")],
    ]
    reply_markup = InlineKeyboardMarkup(keyboard)

    await update.message.reply_text(
        message_text,
        reply_markup=reply_markup,
        parse_mode=ParseMode.MARKDOWN_V2 # Still need to specify ParseMode
    )

    return ASK_FOR_IP # Entra en el estado ASK_FOR_IP de la conversación

async def handle_add_exception_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    """Handles the callback to add a new exception IP."""
    query = update.callback_query
    await query.answer()

    await query.edit_message_text(
        escape_markdown("Por favor, envíame la IP que deseas añadir a la lista de excepciones."),
        parse_mode=ParseMode.MARKDOWN_V2
    )

    return ASK_FOR_IP # Permanece en este estado esperando la IP

async def add_exception_ip(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    """Handles the user providing the IP to add to exceptions."""
    user_input = update.message.text.strip()
    chat_id = update.message.chat_id

    # Validar formato de IP (simple regex, puedes mejorarlo si es necesario)
    if not re.match(r'^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$', user_input):
        await update.message.reply_text(
            escape_markdown(f"❌ *Formato de IP inválido:* `{escape_markdown(user_input)}`\nPor favor, envía una IP válida o /cancelar para salir."),
            parse_mode=ParseMode.MARKDOWN_V2
        )
        return ASK_FOR_IP # Pide la IP de nuevo

    if user_input in exception_ips:
         await update.message.reply_text(
            escape_markdown(f"ℹ️ *La IP* `{escape_markdown(user_input)}` *ya se encuentra en la lista de excepciones.*"),
            parse_mode=ParseMode.MARKDOWN_V2
        )
    else:
        exception_ips.add(user_input)
        # Modificado: Escapar la IP antes de insertarla en la cadena del mensaje
        # Escapar los puntos específicamente para mostrar dentro de backticks en MarkdownV2
        escaped_user_input_for_display = user_input.replace('.', '\.')
        # Construir el mensaje manualmente para evitar problemas de escape con asteriscos y backticks
        message_text = escape_markdown("✅ IP ") + "`" + escaped_user_input_for_display + "`" + escape_markdown(" añadida a la lista de excepciones.")

        await update.message.reply_text(
            message_text,
            parse_mode=ParseMode.MARKDOWN_V2
        )

    return ConversationHandler.END # Termina la conversación

async def cancel_exception_flow(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    """Cancels the process of adding an exception IP."""
    # Determinar si la llamada viene de un CallbackQuery o un Message
    if update.callback_query:
        query = update.callback_query
        await query.answer()
        await query.edit_message_text(
            escape_markdown("❌ *Proceso cancelado.*"),
            parse_mode=ParseMode.MARKDOWN_V2
        )
    else: # Viene de un comando /cancelar
        await update.message.reply_text(
            escape_markdown("❌ *Proceso cancelado.*"),
            parse_mode=ParseMode.MARKDOWN_V2
        )

    return ConversationHandler.END # Termina la conversación

# La función exception_flow_timeout ha sido eliminada ya que timeout_on_file no es un argumento válido.
# Si necesitas manejar un mensaje específico al agotarse el tiempo, deberás implementar un estado de timeout
# dentro de los 'states' del ConversationHandler.

# --- Fin NUEVOS HANDLERS PARA EL COMANDO /excepciones ---


# --- Handler for natural language ---
async def process_natural_language_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Attempts to process text messages that are not commands."""
    message = update.message.text.lower()
    response = None

    # Consider adding spaCy back if more complex language analysis is needed
    # doc = nlp(message)

    # Delegar a los manejadores específicos para aprovechar su lógica completa (ahora usan conexión persistente)
    if "ip" in message and "servidor" in message or re.search(r'\b(cual es (la )?ip|dame la ip|muestra la ip)\b', message):
        await network_status(update, context)
        return

    elif re.search(r'\b(conexion a internet|internet funciona|ping a google|hay internet)\b', message):
        context.args = ["8.8.8.8"]
        await ping(update, context)
        return

    elif any(p in message for p in ["reiníciate", "reiniciar", "reinicio", "vuélvete a encender", "reboot"]):
        await reiniciar(update, context)
        return
    elif any(p in message for p in ["apágame", "apagar", "apagado", "poweroff"]):
        await apagar(update, context)
        return
    elif any(p in message for p in ["memoria", "ram", "uso de memoria"]):
        await memory_usage(update, context)
        return
    elif any(p in message for p in ["disco", "almacenamiento", "uso de disco"]):
        await disk_usage(update, context)
        return
    elif any(p in message for p in ["uptime", "tiempo de actividad", "cuanto tiempo lleva encendido"]):
        await uptime(update, context)
        return
    elif any(p in message for p in ["alertas", "suricata"]):
        await alertas(update, context)
        return
    elif "mitigar" in message or "gestionar alertas" in message or "bloquear ip" in message:
        await mitigar(update, context)
        return
    elif "modo automatico" in message or "modo automático" in message:
         await modo_automatico(update, context)
         return
    elif any(p in message for p in ["está encendido", "está activo", "servidor disponible", "funciona el servidor", "check", "comprueba"]):
        await check(update, context)
        return
    elif "network status" in message or "estado de red" in message or "configuracion red" in message or re.search(r'\b(informacion de red)\b', message):
         await network_status(update, context)
         return
    elif "ping " in message:
        parts = message.split("ping ", 1)
        if len(parts) > 1 and parts[1].strip():
            context.args = [parts[1].strip()]
            await ping(update, context)
            return
        else:
            response = escape_markdown("❌ *Por favor, proporciona una IP o dominio para hacer ping.*")
    elif "exec " in message or "ejecuta " in message:
        command_match = re.search(r'(exec|ejecuta)\s+(.*)', message)
        if command_match and command_match.group(2).strip():
            context.args = command_match.group(2).strip().split()
            await exec_comando(update, context)
            return
        else:
            response = escape_markdown("❌ *Por favor, especifica el comando a ejecutar después de 'exec' o 'ejecuta'.*")
    elif "accesos" in message or "ultimos accesos ssh" in message or re.search(r'\b(quien se ha conectado)\b', message):
        await accesos(update, context)
        return
    # Añadir manejo de lenguaje natural para desbloquear
    elif "desbloquear " in message or "unblock " in message:
        parts = message.split("desbloquear ", 1)
        if len(parts) == 1:
             parts = message.split("unblock ", 1)

        if len(parts) > 1 and parts[1].strip():
             ip_str = parts[1].strip().split()[0]
             context.args = [ip_str]
             await unblock_ip_command(update, context)
             return
        else:
            response = escape_markdown("❌ *Por favor, especifica la IP a desbloquear después de 'desbloquear' o 'unblock'.*")

    else:
        response = escape_markdown("❌ *Comando no reconocido. Aquí están los comandos disponibles:*\n\n") + format_help_message()


    if response:
        await update.message.reply_text(
            response,
            parse_mode=ParseMode.MARKDOWN_V2
        )

async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles all text messages (excluding commands that already have handlers)."""
    if update.message.text and update.message.text.startswith('/'):
        return
    await process_natural_language_message(update, context)

def main():
    """Starts the bot."""
    application = Application.builder().token(TOKEN).build()

    job_queue = application.job_queue
    if job_queue is None:
         print("ERROR: JobQueue no está inicializado. Asegúrate de instalar python-telegram-bot con el extra 'job-queue': pip install 'python-telegram-bot[job-queue]'")
         pass

    if job_queue:
        job_queue.run_once(setup_remote_log_file, 1, name="setup_log")

    # Command Handlers (Note: /excepciones is handled by ConversationHandler)
    application.add_handler(CommandHandler("start", start))
    application.add_handler(CommandHandler("cancelar", cancelar)) # Añadido: Handler para /cancelar
    application.add_handler(CommandHandler("reiniciar", reiniciar))
    application.add_handler(CommandHandler("apagar", apagar))
    application.add_handler(CommandHandler("exec", exec_comando))
    application.add_handler(CommandHandler("network_status", network_status))
    application.add_handler(CommandHandler("ping", ping))
    application.add_handler(CommandHandler("accesos", accesos))
    application.add_handler(CommandHandler("alertas", alertas))
    application.add_handler(CommandHandler("mitigar", mitigar))
    application.add_handler(CommandHandler("memory_usage", memory_usage))
    application.add_handler(CommandHandler("disk_usage", disk_usage))
    application.add_handler(CommandHandler("uptime", uptime))
    application.add_handler(CommandHandler("check", check))
    application.add_handler(CommandHandler("modo_automatico", modo_automatico))
    application.add_handler(CommandHandler("desbloquear", unblock_ip_command))

    # Conversation Handler for /excepciones command <-- Añadido: ConversationHandler para excepciones
    exception_conv_handler = ConversationHandler(
        entry_points=[CommandHandler("excepciones", excepciones)], # Inicia con el comando /excepciones
        states={
            ASK_FOR_IP: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, add_exception_ip), # Espera la IP como texto que no sea comando
                CallbackQueryHandler(handle_add_exception_callback, pattern="^add_exception_ip$"), # Maneja el botón "Añadir nueva IP"
                # El botón de cancelar también se maneja como fallback global
            ],
        },
        fallbacks=[
            CommandHandler("cancelar", cancel_exception_flow), # Permite cancelar con /cancelar en cualquier estado
            CallbackQueryHandler(cancel_exception_flow, pattern="^cancel_exception_flow$"), # Maneja el botón "Cancelar"
        ],
        # Añadir un timeout para la conversación (opcional, pero recomendado)
        conversation_timeout=60, # Timeout de 60 segundos (ajusta según necesites)
        # timeout_on_file=exception_flow_timeout # Eliminado: Argumento no válido
    )

    application.add_handler(exception_conv_handler) # Añadir el handler a la aplicación


    # Callback Query Handlers for mitigation/action flow
    application.add_handler(CallbackQueryHandler(handle_mitigation_choice, pattern="^select_alert_")) # Ahora handle_mitigation_choice está definido
    application.add_handler(CallbackQueryHandler(handle_confirmed_action, pattern="^confirm_action_"))
    application.add_handler(CallbackQueryHandler(handle_cancel_action, pattern="^cancel_action$"))
    application.add_handler(CallbackQueryHandler(handle_auto_mode_callback, pattern="^auto_mode_"))

    # Message Handler for natural language (only processes text that is NOT a command)
    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_message))

    print("Bot is running... Press Ctrl-C to stop.")
    try:
        application.run_polling(poll_interval=1.0, stop_signals=None)
    finally:
        print("Bot detenido. Intentando cerrar conexión SSH.")
        try:
            loop = asyncio.get_running_loop()
            loop.run_until_complete(close_persistent_ssh_connection(application))
        except RuntimeError:
             print("No se encontró un loop de asyncio ejecutándose para cerrar la conexión SSH.")
        except Exception as e:
             print(f"Error durante el intento de cierre de conexión SSH: {e}")

if __name__ == '__main__':
    main()

