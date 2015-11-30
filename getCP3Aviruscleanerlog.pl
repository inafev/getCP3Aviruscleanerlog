#!/usr/bin/perl -w

use strict;
use warnings;
use LWP::UserAgent;
use HTTP::Cookies;
use MLDBM qw(DB_File Data::Dumper);
use Fcntl qw(O_CREAT O_RDWR O_WRONLY O_RDONLY :flock);
use Date::Calc qw(Add_Delta_Days Today Today_and_Now Timezone Add_Delta_YMDHMS);
use IO::File;
use Mail::Mailer;

#################################################################################################################
#	getCP3Aviruscleanerlog.pl - Version: 2.2 - 08/05/2006 - 
#################################################################################################################
#	
# Purpose:	Script que obtiene mediante HTTP GET los logs rotados de viruscleaner de los CP3A (nodos SMTP de Critical Path). Calcula el
# 		número de veces que cada virus ha sido filtrado por el sistema, incluyendo información
#		sobre la clase de virus a la que pertenece (Email-Worm, Net-Worm, Trojan-Downloader, etc).
#
# Platforms:    All Perl platforms should be OK. Tested: Perl 5.8.6 , 5.8.7 and 5.8.8 on Linux and Solaris
#
# Updates:      1.00 First release. (07/04/2006)
#		1.1  Mejora en algoritmo empleado para determinar cuando el resultado estadístico de un fichero
#			de salida .csv es el definitivo y completo para una determinada fecha ("fichero-1.csv")
#		1.2 (19/04/2006)
#			Creación de fichero log con las trazas del script.Fichero log con rotación y compresión en .gz
#			Se incluye el offset con respecto a GMT en los registros de Logs 
#		1.3 (20/04/2006)
#			Redirección de STDERR a un fichero de errores 
#			Se incluye en los logs del script el tamaño de los ficheros log bajados por CP3A
#			Se incluye fecha y hora de errores generados por "die" (redirigido al fichero de errores)
#		1.4 Corrección bug: la segunda base de datos sólo almacenaba las fechas completadas que han sido 
#			eliminadas. El algoritmo comprobaba en esa BBDD si una nueva fecha había sido eliminada 
#			previamente. Mejora: Se almacena sólo la última fecha completada por grupo CP3A, sólo se
#			analizan las fechas que son mayores (más recientes) que la última fecha completada por grupo.
#		1.5 (2006-04-24)
#			Bug: Logs rotados con una misma fecha en el nombre del fichero son del tipo: 
#			cleaner_fecha00.log -> cleaner_fecha01.log -> cleaner_fecha02.log ....
#			Por lo tanto el mismo fichero log va cambiando de nombre y no sabemos cuántos habrán con la
#			misma fecha en el nombre que la de ejecución del script hasta que ese día haya transcurrido.
#			Conclusión: se tratarán todos los logs con fechas en el nombre comprendidas entre un día más
#			que la del último log tratado para ese cp3a, y el día anterior a la ejecución del script.
#			Si se ejecuta para bajar logs el día 25, se intentarán bajar todos los que hay antes del 25
#			que no hayan sido todavía tratados según la BBDD.
#		1.6 (2006-04-26) 
#			Mejora de bajarLogsRotadosAyer()
#		1.7 (2006-04-27)
#			Se incluyen dos nuevos grupos de CP3A: groupA-out y ZZZ-out
#				groupA-out : lista de CP3A para el tráfico de salida de groupA y groupA-pymes
#				ZZZ-out : lista de CP3A para el tráfico de salida de ZZZ y ZZZ-pymes
#			Mejora de analizarFicherosLogExistentes()
#		2.0 (2006-05-03) 
#			Viruscleaner utiliza Log4j para el rotado de logs. Log4j es flexible y configurable.
#			Se solicita a Soporte de Critical Path el rotado de logs de VirusCleaner basado en la fecha en
#			lugar del tamaño. De este modo cada día a las 00:00 h se generará un fichero log rotado con los
# 			únicamente logs del día que acaba de terminar. Consecuencias: Se simplifica el algoritmo del
#			script, se obtienen antes los resultados, y se evita pérdida de datos. Ya NO es necesario
#			tener dos hashes para analizar cuándo una fecha está "completada" (no se esperan nuevos
#			registros en los logs con esa fecha). NUEVO ALGORITMO: Se bajan los logs rotados el día
#			anterior y se analizan.
#		2.1 (2006-05-04 y 2006-05-05)
#			- Se incluye envío de un email informativo por ejecución de "-downloadlogs" y "-loganalysis"
#			- Pequeña mejora en los logs del script de la rutina bajarLogsRotadosEnUnaFecha()
#			- Se comprueba con un "if (exists($databaseLogsBajados{$cp3a}{"cleaner_".$date."xx.log"}))" si
#			un log ha sido bajado anteriormente en otra ejecución del script. De este modo se evita que
# 			dos ejecuciones simultáneas y en el mismo día de "-downloadlogs" incluya datos replicados a
#			ser analizados
#			- Si un fichero .csv para un grupo CP3A y una fecha ya existe, no se vuelve a generar con
#			los nuevos datos descargados y en registra un error en los logs.
#		2.2 (2006-05-08)
#			- Mejora de rutina bajarLogsRotadosEnUnaFecha() . Se descargan los logs de viruscleaner
#			directamente a un fichero temporal, en lugar de hacerlo en memoria. De esta manera se 
#			mejora el consumo de memoria del script, de 67MB pasa a utilizar 11MB.
#			- Uso de "$ua->agent('Mozilla/5.0');" para hacerse pasar por el navegador web de mozilla
#			- Uso de "if ($response->content_type( ) eq "save/application")" como condición para saber
#			cuando un log rotado existe en el servidor y puede ser bajado si no hay un error.
#
#
# Author        : Iñaki Fernández, openerpappliance@gmail.com , www.openerpappliance.com
#                 
#
# DESCRIPCIÓN DEL SCRIPT: 
# Actualmente no es posible listar por cada CP3A los logs de virus cleaner existentes (ni con HTTP ni con MGR). El 
# único método de acceso para su descarga es a través de HTTP. En cada CP3A el log 
# cp3a_cleaner.log es el que está siendo actualizado durante el día, y a las 00:00 h cuando se cambia de día
# es rotado con la fecha en el nombre del fichero del día que ha terminado (por ejemplo "cleaner_2006042501.log"
# contiene únicamente registros con fecha 2006-04-25 y ha rotado al final de ese día).
#
# VARIABLES GLOBALES DEL SCRIPT MODIFICABLES:
# Este script almacena por defecto y temporalmente los logs bajados de los CP3A en el path de la variable
# $pathCp3aLogs, y el resultado del análisis de los logs en el path de la variable $pathresultadoestadisticas. 
# Si se desea cambiar el path de ambos directorios sólo hay que modificar estas dos variables definidas al principio
# del script con el resto de variable globales modificables.
#
# Las variables modificables $ficheroListaCp3aXXX, $ficheroListaCp3aZZZ, $ficheroListaCp3aXXXPymes,
# $ficheroListaCp3aZZZPymes, $ficheroListaCp3aXXXOut y $ficheroListaCp3aZZZOut son las que contienen el nombre 
# de los 6 ficheros, uno por grupo de CP3A, con la lista de IPs o nombres DNS de los CP3A a consultar. 
# Estos ficheros sólo se utilizarán con la opción "-initdb" del script, para inicializar la BBDD con la lista de CP3A.
#
# GRUPOS DE CP3A:
#	XXX : Los CP3A para tráfico SMTP ENTRANTE de XXX (CSMTPMX)
#	XXX-pymes : Los CP3A para tráfico SMTP ENTRANTE de XXX-PYMES (CPYSMTPMX)
#	groupA-out : Los CP3A para el tráfico SMTP SALIENTE de XXX y XXX-PYMES (CSMTPOUT)
#	ZZZ : Los CP3A para tráfico SMTP ENTRANTE de ZZZ (CTSMTPMX)
#	ZZZ-pymes : Los CP3A para tráfico SMTP ENTRANTE de ZZZ-PYMES (CTPYSMTPMX)
#	ZZZ-out : Los CP3A para el tráfico SMTP SALIENTE de ZZZ y ZZZ-PYMES (CTSMTPOUT)
#
# AÑADIR UN NUEVO CP3A A LA LISTA DE NODOS DE UN GRUPO CP3A:
# Si hay que añadir un nuevo CP3A en un grupo es necesario modificar su fichero de texto correspondiente y utilizar 
# la opción "-initdb".
#
# USO DEL SCRIPT:
# La información de uso del script se obtiene si se ejecuta sin ningún argumento ó con uno erróneo.
#
# REQUISITOS DE ESPACIO EN DISCO:
# Logs del script: Tamaño máximo definido en variable global modificable $maxLogFileSize, y con número máximo
# de rotado de logs en variable $numFicherosLogRotados
# Logs de viruscleaner bajados de los CP3A: Es aconsejable ejecutar 1 vez todas las noches el script para bajarse
# y analizar los logs rotados el día anterior. Son eliminados una vez que se analizan en esa misma noche.
#
# CONSUMO DE RECURSOS (MEMORIA Y CPU) EN CONDICIONES NORMALES:
# El consumo de CPU puede variar entre 0.01% y 4.5%, y el de memoria sobre unos 11M
# Por ejemplo véase la siguiente salida del comando top:
#   PID USERNAME THR PRI NICE  SIZE   RES STATE    TIME    CPU COMMAND
#  13415 mta       1  58    0   11M   11M sleep    0:26  2.54% getCP3Aviruscle
#
# EJEMPLO DEL CONTENIDO DE LA BBDD EN EL HASH %databaseLogsBajados PARA EL GRUPO CP3A ZZZ-PYMES:
# Se utiliza un hash persistente (MLDBM) para registrar los logs bajados por CP3A.
# (obtenido con "./getCP3Aviruscleanerlog.pl -printdb ZZZ-pymes" tras ejecutar el script con "-initdb"):
#
#$VAR1 = {
#          'ctpysmtpmx1.adm.correo' => {
#                                        'cleaner_20060502xx.log' => '8388663'
#                                      },
#          'ctpysmtpmx2.adm.correo' => {
#                                        'cleaner_20060502xx.log' => '8388764'
#                                      },
#          'ctpysmtpmx3.adm.correo' => {
#                                        'cleaner_20060502xx.log' => '8388665'
#                                      },
#          'ctpysmtpmx4.adm.correo' => {
#                                        'cleaner_20060101xx.log' => 0
#                                      },
#          'ctpysmtpmx5.adm.correo' => {
#                                        'cleaner_20060502xx.log' => '8388614'
#                                      }
#        };
#
# Donde: De ctpysmtpmx4.adm.correo no ha sido posible descargar el log con fecha del día anteior (20060502). 
# En la última columna se registra el tamaño en bytes del fichero log bajado.
#
# RESULTADO: Los ficheros estadísticos resultantes terminan en ".csv", por ejemplo
# "estadisticas-cp3a-viruscleaner-XXX-20060405.csv" , y se pueden encontrar en el path definido en la variable
# global modificable $pathresultadoestadisticas . Unas líneas de ejemplo de un fichero .csv del grupo XXX:
#
#	Win32.NetSky.q|87837|Email-Worm
#	Win32.NetSky.r|10056|Email-Worm
#	Win32.NetSky.d|6656|Email-Worm
#	Win32.NetSky.b|4198|Email-Worm
#	Win32.Zafi.d|3683|Email-Worm
#	Win32.NetSky.aa|3106|Email-Worm
#
# NOTA: Mientras se ejecuta el script con un argumento no se puede ejecutar de nuevo el script. Si el script
# está bajando logs de CP3A ó analizándolos no se podrá imprimir el contenido de las BBDD hasta que termine
# la primera ejecución del mismo (se puede intentar, pero el comando no responderá hasta que termine el primero).
#
# NOTA2: En Perl 5.8.x existe un posible bug que genera el siguiente warning (redirigido al fichero 
# $errorsLogFile):
# Solaris, Perl 5.8.7:
# 	Argument "2.121_04" isn't numeric in subroutine entry at
#	/usr/local/lib/perl5/5.8.7/sun4-solaris/Data/Dumper.pm line 5
# Linux, Perl 5.8.6 y 5.8.8:
# 	Argument "2.121_08" isn't numeric in subroutine entry at 
#	/usr/lib/perl5/5.8.8/i386-linux-thread-multi/Data/Dumper.pm line 5
# Este warning se puede generar cada vez que se imprime por pantalla las BBDD con  "print Data::Dumper->...".
# No es relevante y no afecta al funcionamiento de este script. 
#
#################################################################################################################

# V A R I A B L E S   M O D I F I C A B L E S

# PATH DEL SCRIPT:
my $pathScript = "/home/inaki/utils/scripts-admin/getlogsCP3A";

# PATH (DIRECTORIOS) DE LOS FICHEROS LOG BAJADOS Y PATH DONDE SE CREAN LOS FICHEROS CON LOS RESULTADOS DEL ANALISIS 
# DE LOGS :
my $pathCp3aLogs = "$pathScript/cp3alogs";
my $pathresultadoestadisticas = "$pathScript/resultadoestadisticas";
my $pathMLDBMfiles = "$pathScript";

# Directorio donde se encuentran los logs del script :
my $LOG_DIR = "$pathScript/scriptlogs/";
# Nombre del fichero log del script :
my $log_filename = "$LOG_DIR/getCP3Aviruscleanerlog.log";
# Fichero log con la salida STDERR del script (errores generados en script con p.e. "die" si no hay acceso a un
# fichero) :
my $errorsLogFile = "$LOG_DIR/errors.log"; 

# TAMAÑO MÁXIMO PARA EL FICHERO LOG DEL SCRIPT. Una vez superado este tamaño el fichero log del script rotará.
# (Se comprueba el tamaño del fichero log del script únicamente en cada ejecución de script con las opciones
# -downloadlogs ó -loganalysis)
my $maxLogFileSize = 10000000;	# 100000 = 100Kbytes ,  10000000 = 10Mbytes
#Numero de Ficheros Log del script en rotación (Si pongo 3 rotación será: file->file.0->file.1->file.2->file.3)
my $numFicherosLogRotados = 3;	

#TAMAÑO MÁXIMO PARA EL FICHERO DE ERRORES DEL SCRIPT
my $maxErrorsLogFileSize = 500000;	# 100000 = 100Kbytes ,  10000000 = 10Mbytes
#Numero de Ficheros Log del script en rotación (Si pongo 3 rotación será: file->file.0->file.1->file.2->file.3)
my $numFicherosLogDeErroresRotados = 2;	

# SE DESEA COMPRIMIR LOS FICHEROS LOG ROTADOS?:
my $compressLogFiles = 1;	# 0 si no se quiere comprimir los fichero log rotados

# VARIABLES QUE CONTIENEN LOS 4 FICHEROS INICIALES CON EL LISTADO DE MAQUINAS CP3A EN CADA UNO DE LOS GRUPOS
#my $ficheroListaCp3aXXX = "$pathScript/cp3a-XXX.txt";
#my $ficheroListaCp3aXXXPymes = "$pathScript/cp3a-XXX-pymes.txt";
#my $ficheroListaCp3aZZZPymes = "$pathScript/cp3a-ZZZ-pymes.txt";
#my $ficheroListaCp3aZZZ = "$pathScript/cp3a-ZZZ.txt";
# Los siguientes ficheros contienen las mismas entradas que los anteriores pero con nombres DNS:
my $ficheroListaCp3aXXX = "$pathScript/cp3a-XXX-hostnames.txt";
my $ficheroListaCp3aXXXPymes = "$pathScript/cp3a-XXX-pymes-hostnames.txt";
my $ficheroListaCp3aXXXOut = "$pathScript/cp3a-groupA-out-hostnames.txt";
my $ficheroListaCp3aZZZ = "$pathScript/cp3a-ZZZ-hostnames.txt";
my $ficheroListaCp3aZZZPymes = "$pathScript/cp3a-ZZZ-pymes-hostnames.txt";
my $ficheroListaCp3aZZZOut = "$pathScript/cp3a-ZZZ-out-hostnames.txt";

# VARIABLE GLOBAL UTILIZADA EN RUTINA borrarAntiguosLogsBajados() PARA BORRAR DE LA BBDD DE FICHEROS LOG BAJADOS POR
# CP3A AQUELLOS FICHEROS LOG CUYA FECHA DIFIERA EN MAS DE $numDiasMaxEnBBDDdeLogs CON RESPECTO AL ULTIMO LOG BAJADO
# PARA ESE MISMO CP3A
my $numDiasMaxEnBBDDdeLogs = 60;

# VARIABLES GLOBALES PARA LA CONFIGURACION DE ENVÍO DE EMAIL INFORMATIVO:
my $mailserver = 'smtpplaXYXY.domain.local';	# servidor SMTP
my $from_mail_address = 'ifernandez@YYY.com';	# Dirección del remitente
my $to_mail_address = 'ifernandez@YYY.com';	
my $to_mail_address2 = 'ibbbbb@gmail.com';
# Lista de usuario a quien enviar el correo informativo:
#my @list_to_addresses = [$to_address,$to_address2,'user1@dominio.com','user2@dominio.com','user3@dominio.com'];
my @list_to_mail_addresses = [$to_mail_address,$to_mail_address2];

# VARIABLES GLOBALES PARA LA DESCARGA DE LOGS DE CADA CP3A MEDIANTE HTTP GET:
# No descarga ficheros log del tamaño superior a la siguiente variable:
my $maxBytesOfCp3aLogFile = 100000000;	 # 100000000 = 100 Mbytes
# Timeout de HTTP Get:
my $timeoutInSecsOfHttpGet = 15; # Por defecto son 180 segundos (3 min)


#################################################################################################################
#################################################################################################################
# 			CONTENIDO DEL SCRIPT. NO MODIFICAR
#################################################################################################################
#################################################################################################################

# ES NECESARIO ROTAR EL FICHERO DE ERRORES?:
my $errorslogFileSize = -s $errorsLogFile;

if ((defined($errorslogFileSize)) && ( $errorslogFileSize > $maxErrorsLogFileSize ))
{	# Rotado de logs pq ha superado el tamaño máximo especificado
&rotatelogs($errorsLogFile,$numFicherosLogDeErroresRotados);
# compress the newly rotated files if requested:
if ($compressLogFiles) { system "gzip $errorsLogFile.0"; }
}

# LO PRIMERO: REDIRIGIR LA SALIDA DE ERRORES AL FICHERO DE ERRORES:
open(STDERR, ">>$errorsLogFile") || die "ERROR en script getCP3Aviruscleanerlog.pl del grupo CORREO XXX en TDATA: No se puede acceder al fichero de errores \"$errorsLogFile\" => $!";

# LO SEGUNDO: Calcular la fecha y hora de inicio de ejecución del script (para logs del scrip y salida de errores):
my $gmt=1; # VOY A CALCULAR LA FECHA DE HOY PERO EN GMT
my ($year,$month,$day,$hour,$min,$sec) = Today_and_Now([$gmt]);
# Calculo el offset con respecto a GMT, p.e. "0,0,0, 2,0,0, 1" en abril	:
my ($D_y,$D_m,$D_d, $Dh,$Dm,$Ds, $dst) = Timezone(); 
# Añado a la fecha el offset con GMT (1 ó 2 horas según mes del año):
($year,$month,$day, $hour,$min,$sec) = Add_Delta_YMDHMS($year,$month,$day, $hour,$min,$sec,$D_y,$D_m,$D_d, $Dh,$Dm,$Ds);
# VARIABLE GLOBAL para utilizada en comandos "die" (con salida de STDERR)
my $fechayhoraInicioEjecucionScript = sprintf "%4d-%02d-%02d %02d:%02d:%02d",$year,$month,$day,$hour,$min,$sec;


# FICHERO LOG DEL SCRIPT, INCLUYENDO ROTADO DE LOGS SI ES NECESARIO:
my $logFileSize = -s $log_filename;

if ((defined($logFileSize)) && ( $logFileSize > $maxLogFileSize ))
{	# Rotado de logs pq ha superado el tamaño máximo especificado
&rotatelogs($log_filename,$numFicherosLogRotados);
# compress the newly rotated files if requested:
if ($compressLogFiles) { system "gzip $log_filename.0"; }
}

open (LOGHANDLE, ">>" . $log_filename) or die ("$fechayhoraInicioEjecucionScript cannot append ".$log_filename.":".$!);
flock(LOGHANDLE, LOCK_EX);	#locking the file 

select LOGHANDLE;	
# Todos los "print" sin filehandle específico, serán dirigidos POR DEFECTO al filehandle seleccionado en ésta 
# línea (LOGHANDLE, fichero log).En el script se utiliza "select filehandle" según adónde se quiera dirigir la salida 
$| = 1;  # don't keep LOG entries sitting in the buffer
#by default, the output to each filehandle is buffered. Setting the special $| variable to 1 will set the selected
# filehandle (the one selected at the time the variable is modified) to flush the buffer after each output operation

# VARIABLES GLOBALES:
my $ficheroListaCp3a;
my $numArgs = $#ARGV + 1; # Número de argumentos pasado al script
#print "thanks, you gave me $numArgs command-line arguments.\n";
my $dateOfLogString;
my $allcp3agroups=0; # 1 si hay que bajar y analizar los logs de todos los grupos cp3a
my $initDBofThisCp3a; # Variable global para el caso de que se quiera inicializar únicamente la bbdd de un único
			# cp3a ("-initcp3adb")

if (($numArgs == 2) && (($ARGV[0] eq "-initdb") || ($ARGV[0] eq "-downloadlogs") || ($ARGV[0] eq "-loganalysis") || ($ARGV[0] eq "-printdb")) && (($ARGV[1] eq "XXX") || ($ARGV[1] eq "ZZZ") || ($ARGV[1] eq "XXX-pymes") || ($ARGV[1] eq "ZZZ-pymes") || ($ARGV[1] eq "groupA-out") || ($ARGV[1] eq "ZZZ-out") || ($ARGV[1] eq "all")) )
{
	if ($ARGV[0] eq "-printdb")
	{ 
	# Selección de dónde escribir la salida creada con print (salida estándar en lugar del fichero log por defecto):
	select STDOUT;
	}
	if ($ARGV[1] eq "all") { $allcp3agroups = 1; }
}
elsif ( ($numArgs == 3) && ($ARGV[0] eq "-downloadlogs") && (($ARGV[1] eq "XXX") || ($ARGV[1] eq "ZZZ") || ($ARGV[1] eq "XXX-pymes") || ($ARGV[1] eq "ZZZ-pymes") || ($ARGV[1] eq "groupA-out") || ($ARGV[1] eq "ZZZ-out") || ($ARGV[1] eq "all")) )
{ 
	if ($ARGV[1] eq "all") { $allcp3agroups = 1; }
	$dateOfLogString = $ARGV[2];
	if (!($dateOfLogString =~ /\b\d{8}\b/))
	{
		print STDOUT "ERROR: FECHA INCORRECTA\n"; 
		print STDOUT "Ejemplo: ./getCP3Aviruscleanerlog.pl -downloadlogs XXX 20060329 \n";
		exit 1;
	}
}
elsif ( ! ( ($numArgs == 2) && (($ARGV[0] eq "-loganalysis") || ($ARGV[0] eq "-downloadlogs") || ($ARGV[0] eq "-printdb"))
&& (($ARGV[1] eq "XXX") || ($ARGV[1] eq "ZZZ") || ($ARGV[1] eq "XXX-pymes") || ($ARGV[1] eq "ZZZ-pymes") || ($ARGV[1] eq "groupA-out") || ($ARGV[1] eq "ZZZ-out") ) ) )
{
 	print STDOUT "SCRIPT PARA EL ANÁLISIS DE LOGS DE VIRUS CLEANER DE LOS CP3A\n";
	#print "------------------------------------------------------------\n";
	print STDOUT "ERROR!. MODO DE USO:\n";
	print STDOUT "./getCP3Aviruscleanerlog.pl -initdb grupoCP3A \t (Inicializa BBDD con los CP3A del grupo especificado)\n";
	print STDOUT "./getCP3Aviruscleanerlog.pl -initdb all \t\t (Inicializa BBDD de todos los CP3A)\n";
	print STDOUT "./getCP3Aviruscleanerlog.pl -downloadlogs grupoCP3A \t\t (baja logs del grupo CP3A especificado)\n";
	print STDOUT "./getCP3Aviruscleanerlog.pl -downloadlogs grupoCP3A fechalog \t (baja logs del grupo CP3A que hayan rotado en la fecha especificada)\n";
	print STDOUT "./getCP3Aviruscleanerlog.pl -downloadlogs all fechalog \t (idem, para todos los grupos)\n";
	print STDOUT "./getCP3Aviruscleanerlog.pl -loganalysis grupoCP3A \t\t (analiza logs del grupo CP3A especificado)\n";
	print STDOUT "./getCP3Aviruscleanerlog.pl -printdb grupoCP3A \t\t (imprime BBDD de logs bajados del grupo CP3A especificado)\n";
	print STDOUT "./getCP3Aviruscleanerlog.pl -downloadlogs all \t\t (baja logs de todos los CP3A)\n";
	print STDOUT "./getCP3Aviruscleanerlog.pl -loganalysis all \t\t (analiza logs de todos los CP3A)\n";
	print STDOUT "./getCP3Aviruscleanerlog.pl -printdb all \t\t (imprime BBDD de logs bajados de todos los CP3A)\n";
	#print "\n";
	print STDOUT "DONDE:\n";
	print STDOUT "grupoCP3A = XXX , ZZZ , XXX-pymes , ZZZ-pymes , groupA-out ó ZZZ-out\n";
	print STDOUT "fechalog = AAAAMMDD , ejemplo: 20060329\n";
	print STDOUT "Ejemplo: ./getCP3Aviruscleanerlog.pl -loganalysis ZZZ \n";
	print STDOUT "Ejemplo: ./getCP3Aviruscleanerlog.pl -downloadlogs XXX-pymes \n";
	print STDOUT "Ejemplo: ./getCP3Aviruscleanerlog.pl -downloadlogs XXX 20060329 \t";
	print STDOUT "Ejemplo: ./getCP3Aviruscleanerlog.pl -initdb all \n";
	print STDOUT "Ejemplo: ./getCP3Aviruscleanerlog.pl -downloadlogs all\n";
	print STDOUT "\n";
	print STDOUT "Nota 1: \"-initdb\" borra la base de datos si ya existe y crea una nueva con la lista de cp3a de los\n";
	print STDOUT "	6 ficheros de texto especificados en el script, por ejemplo \"cp3a-XXX-hostnames.txt\" \n";
	print STDOUT "	Una vez que se ha inicializado la bbdd el script obtendrá la lista de CP3a de la propia bbdd\n";
	print STDOUT " 	\"-initdb\" borra también los ficheros log globales existentes como por ejemplo viruscleaner_all_XXX_2006-04-05.log\n";
	print STDOUT "Nota 2: El path donde se bajan los ficheros log y el path donde se crean los ficheros .csv con el\n";
	print STDOUT "	resultado del análisis de virus, se especifican también en el script en las variables\n";
	print STDOUT "	\$pathCp3aLogs y \$pathresultadoestadisticas \n";
	print STDOUT "Ver primeras líneas del script para más información\n";
	exit 1;
}

######################################################################################################################
#	HASHES PERSISTENTES (VARIABLES GLOBALES ACCESIBLES POR TODAS LAS RUTINAS SIN PASAR PARÁMETROS)
######################################################################################################################
#Hash persistente (mldbm) donde ser guarda la bbdd de los logs bajados y tratados de los grupos de CP3A para poder
#consultar a posteriori ésta información:
my %databaseLogsBajados;

######################################################################################################################

printf "%s\n","="x80;
printf "$fechayhoraInicioEjecucionScript NUEVA EJECUCIÓN DEL SCRIPT!\n";

if ($allcp3agroups) { 	
	print  "TRATANDO TODOS LOS GRUPOS DE CP3A\n";
}
printf "%s\n","="x80;

# LISTA de Grupos de CP3A con los que hay que tratar:
my @listOfCP3AGroupsToWorkWith;
# Variable que contiene el grupo de cp3a a tratar:
my $groupCP3A;
# Variable con la fecha de los logs rotados a bajar:
my ($yearToDownload,$monthToDownload,$dayToDownload);
# Variable global con los CP3A que han tenido una respuesta de error de HTTP GET
my @listaCp3aInaccesibles;

# Se cumple la condición "$numArgs > 1"

if ($allcp3agroups)	#Tratar todos los grupos de CP3A
{
push(@listOfCP3AGroupsToWorkWith,"XXX");
push(@listOfCP3AGroupsToWorkWith,"ZZZ");
push(@listOfCP3AGroupsToWorkWith,"XXX-pymes");
push(@listOfCP3AGroupsToWorkWith,"ZZZ-pymes");
push(@listOfCP3AGroupsToWorkWith,"groupA-out");
push(@listOfCP3AGroupsToWorkWith,"ZZZ-out");
}
else
{
push(@listOfCP3AGroupsToWorkWith,$ARGV[1]); # Solo analizar el grupo de CP3A especificado en linea de comandos
}
print  "LISTA DE CP3A A ANALIZAR ES: @listOfCP3AGroupsToWorkWith \n" or die ("$fechayhoraInicioEjecucionScript Cannot print: " . $log_filename . ":" . $!);
foreach $groupCP3A (@listOfCP3AGroupsToWorkWith) 
{
	print  "SE VA A TRATAR EL GRUPO CP3A $groupCP3A\n";
	#printf  "%s\n","-"x80;
	for ($groupCP3A) {
		/\bXXX-pymes\b/    and do { $ficheroListaCp3a = $ficheroListaCp3aXXXPymes; last; } ;
		/\bZZZ-pymes\b/    and do { $ficheroListaCp3a = $ficheroListaCp3aZZZPymes; last; } ;
		/\bgroupA-out\b/    and do { $ficheroListaCp3a = $ficheroListaCp3aXXXOut; last; } ;
		/\bZZZ-out\b/    and do { $ficheroListaCp3a = $ficheroListaCp3aZZZOut; last; } ;
	  	/\bXXX\b/    and do { $ficheroListaCp3a = $ficheroListaCp3aXXX; last; } ;
		/\bZZZ\b/    and do { $ficheroListaCp3a = $ficheroListaCp3aZZZ; last; } ;
	}
	# HAGO UN TIE DEL HASH DE LA BBDD
	my $dbm_filename = "$pathMLDBMfiles/mldbmDownloadedLogs-$groupCP3A.dat";
	tie %databaseLogsBajados, 'MLDBM', $dbm_filename, O_CREAT | O_RDWR, 0666 or die "$fechayhoraInicioEjecucionScript Can't open MLDBM file: $!\n";

	@listaCp3aInaccesibles = ();	# Inicializo la lista por grupo cp3a

	if ($ARGV[0] eq "-initdb")
	{
	#Inicializo base de datos
	# IMPORTANTE: EL ARGUMENTO "-initdb" SOLO SE UTILIZA CUANDO SE QUIERE CARGAR UNA NUEVA LISTA DE CP3A
	# POR GRUPO 
	# En esta BBDD se almacenarán por cada CP3A los logs bajados para su posterior análisis
	# Esta opción borrará la bbdd anterior si existiera.
		&inicializarHashMLDBM($groupCP3A,$ficheroListaCp3a);
	}
	elsif ($ARGV[0] eq "-loganalysis") 
	{
		#print  "ANALIZANDO LOGS...\n";
		my @ficheros_csv_creados = &analizarFicherosLogExistentes($groupCP3A);	#Analizo los Logs
		my $numOfNewFiles = $#ficheros_csv_creados + 1;
		if ($numOfNewFiles > 0)
		{
			# Obtengo en un array el contenido de los nuevos ficheros csv:
			my @body;
		push (@body,"Se ha ejecutado \"$pathScript/getCP3Aviruscleanerlog.pl -loganalysis $groupCP3A\" en el dia y hora $fechayhoraInicioEjecucionScript\n");
		push (@body,"-------------------------------------------------------------------------------\n");
			foreach my $fileitem (@ficheros_csv_creados) 
			{
				push (@body,"\nNUEVO FICHERO .csv CREADO: $fileitem:\n\n");
			open (F,"$fileitem") or die "$fechayhoraInicioEjecucionScript Couldn't open $fileitem: $!";
				while (<F>) {
					push (@body,"$_");
				}
				close F;
			}
			# ENVIO UN MAIL CON INFORMACION:
			my $subject = "CP3A Viruscleaner, Grupo $groupCP3A -> Análisis de datos descargados previamente";
			my $mailer = new Mail::Mailer 'smtp', Server => $mailserver;
			$mailer->open({ From    => $from_mail_address,
                                  To      => @list_to_mail_addresses,
                                  Subject => $subject,
                                })
      			or die "Can't open: $!\n";
			print $mailer @body;
			$mailer->close( );
		}
	}
	elsif ($ARGV[0] eq "-printdb") 
	{
		print "IMPRIMIENDO CONTENIDO DE BBDD DEL GRUPO $groupCP3A:\n";
		#printf  "%s\n","*"x80;
		#set to a boolean value to control whether hash keys are dumped in sorted order
		$Data::Dumper::Sortkeys = 1;	
		print Data::Dumper->Dump([\%databaseLogsBajados]);
	}
	elsif (($numArgs == 3) && ($ARGV[0] eq "-downloadlogs"))
	{ # bajarse los logs rotados en la fecha especificada
		print "ALGORITMO EMPLEADO: Por cada CP3A se intentará bajar el log rotado el día especificado ($dateOfLogString) que contiene únicamente registros de virus tratados en esa misma fecha\n";
		($yearToDownload,$monthToDownload,$dayToDownload) = ($dateOfLogString =~ /(\d\d\d\d)(\d\d)(\d\d)/);
		&bajarLogsGrupoCP3ARotadosEnUnaFecha($groupCP3A,$yearToDownload,$monthToDownload,$dayToDownload);
		my $dateToDownload = sprintf "%4d%02d%02d",$yearToDownload,$monthToDownload,$dayToDownload;
		printf  "%s\n","|"x80;
		my @listaDeCp3aNoUtilizadosEnAnalisis = &listarCp3aSinLogDeUnaFechaRegistradoEnBBDD($dateToDownload);
		print "- Lista de nodos CP3A del grupo $groupCP3A de los que no ha sido posible obtener datos con fecha $dateToDownload: @listaDeCp3aNoUtilizadosEnAnalisis \n";
		print "- Lista de nodos CP3A del grupo $groupCP3A con los que ha habido errores al descargar logs con HTTP GET en esta ejecución: @listaCp3aInaccesibles \n";	
		printf  "%s\n","|"x80;
		printf  "%s\n","/"x80;
		print  "Borrando de la BBDD los ficheros de log bajados más antiguos con respecto al último log bajado (ver variable \$numDiasMaxEnBBDDdeLogs en script)...\n";  
		&borrarAntiguosLogsBajados($groupCP3A,$numDiasMaxEnBBDDdeLogs);	
		printf  "%s\n","/"x80;
		# ENVIO UN MAIL CON INFORMACION:
		&envioMailDescargaLogs($groupCP3A,$dateToDownload,@listaDeCp3aNoUtilizadosEnAnalisis);
	}
	else  # -downloadlogs del día anterior
	{
	print "ALGORITMO EMPLEADO: Por cada CP3A se intentará bajar el log rotado ayer que contiene únicamente registros de virus tratados ayer\n";
	# Calculo la fecha de ayer:
	($yearToDownload,$monthToDownload,$dayToDownload) = Add_Delta_Days($year,$month,$day,-1); 
	#Algoritmo: Bajar log rotados en la fecha de ayer
	&bajarLogsGrupoCP3ARotadosEnUnaFecha($groupCP3A,$yearToDownload,$monthToDownload,$dayToDownload);
	my $dateToDownload = sprintf "%4d%02d%02d",$yearToDownload,$monthToDownload,$dayToDownload;
	printf  "%s\n","|"x80;
	my @listaDeCp3aNoUtilizadosEnAnalisis = &listarCp3aSinLogDeUnaFechaRegistradoEnBBDD($dateToDownload);
	print "- Lista de nodos CP3A del grupo $groupCP3A de los que no ha sido posible obtener datos con fecha $dateToDownload: @listaDeCp3aNoUtilizadosEnAnalisis \n";
	print "- Lista de nodos CP3A del grupo $groupCP3A con los que ha habido errores al descargar logs con HTTP GET en esta ejecución: @listaCp3aInaccesibles \n";	
	printf  "%s\n","|"x80;
	printf  "%s\n","/"x80;
	print  "Borrando de la BBDD los ficheros de log bajados más antiguos con respecto al último log bajado (ver variable \$numDiasMaxEnBBDDdeLogs en script)...\n";
	&borrarAntiguosLogsBajados($groupCP3A,$numDiasMaxEnBBDDdeLogs);	
	printf  "%s\n","/"x80;
	# ENVIO UN MAIL CON INFORMACION:
	&envioMailDescargaLogs($groupCP3A,$dateToDownload,@listaDeCp3aNoUtilizadosEnAnalisis);
	}
	untie %databaseLogsBajados;
	printf  "%s\n","-"x80;
}

($year,$month,$day,$hour,$min,$sec) = Today_and_Now([$gmt]);
# Añado a la fecha el offset con GMT (1 ó 2 horas según mes del año):
($year,$month,$day, $hour,$min,$sec) = Add_Delta_YMDHMS($year,$month,$day, $hour,$min,$sec,$D_y,$D_m,$D_d, $Dh,$Dm,$Ds);
printf "%4d-%02d-%02d %02d:%02d:%02d FINAL DE EJECUCIÓN DEL SCRIPT\n",$year,$month,$day,$hour,$min,$sec;
printf  "%s\n","="x80;

# CIERRO FICHERO LOG DEL SCRIPT:
close LOGHANDLE or die ("$fechayhoraInicioEjecucionScript Cannot close: " . $log_filename . ":" . $!);


#########################################################################################################
# FINAL DEL PROGRAMA PRINCIPAL
#########################################################################################################
#########################################################################################################
#########################################################################################################
# 				S U B R U T I N A S
#########################################################################################################
sub envioMailDescargaLogs
{
my ($groupCP3A,$dateToDownload,@listaDeCp3aNoUtilizadosEnAnalisis) = @_;
my $subject = "CP3A Viruscleaner, Grupo $groupCP3A -> Descarga de logs con getCP3Aviruscleanerlog.pl";
my $body = "Se ha ejecutado \"$pathScript/getCP3Aviruscleanerlog.pl -downloadlogs $groupCP3A\" en el dia y hora $fechayhoraInicioEjecucionScript\n-------------------------------------------------------------------------------\n\n- Lista de nodos CP3A del grupo $groupCP3A de los que no ha sido posible obtener datos con fecha $dateToDownload: @listaDeCp3aNoUtilizadosEnAnalisis\n- Lista de nodos CP3A del grupo $groupCP3A con los que ha habido errores al descargar logs con HTTP GET en esta ejecucion: @listaCp3aInaccesibles\n\n- Ultimos Logs Bajados por CP3A y su tamanio en bytes:\n";

my $mailer = new Mail::Mailer 'smtp', Server => $mailserver;
$mailer->open({ From    => $from_mail_address,
                                To      => @list_to_mail_addresses,
                                Subject => $subject,
                              })
or die "Can't open: $!\n";
print $mailer $body;
#set to a boolean value to control whether hash keys are dumped in sorted order:
$Data::Dumper::Sortkeys = 1;
print $mailer Data::Dumper->Dump([\%databaseLogsBajados]);
$mailer->close( );
}


sub inicializarHashMLDBM
{
my ($groupCP3A,$listofcp3afile) = @_;

open (FILE, "$listofcp3afile")
            or die "$fechayhoraInicioEjecucionScript Couldn't open $listofcp3afile: $!";

#Elimino contenido de la BBDD (es un hash):
%databaseLogsBajados = ( );

#Elimino todos los ficheros Log Globales existentes:
my @log_files = glob "$pathCp3aLogs/viruscleaner_all_$groupCP3A\_*.log";
foreach my $fileitem (@log_files)
{
		if (unlink($fileitem)) {
			print  "Fichero log global $fileitem ha sido eliminado\n";
		} else {
			print  "ERROR:Fichero log global $fileitem NO ha podido ser borrado.\n";
		}
}

while (<FILE>) {
	s/#.*//;              # Remove comments
	s/^\s+//g;   # So long, leading whitespace
	s/\s+$//g;   # So long, trailing whitespace
	next unless /\S/;     # Skip blank lines

	my $cp3a = $_;	
	# Necesario introducir al menos un dato en el "hash of hashes"...
	# Introduzco una fecha antigua que será a posteriori eliminada por la rutina borrarAntiguosLogsBajados()
	my $entry = $databaseLogsBajados{$cp3a};                   # Get
	$entry->{"cleaner_20060101xx.log"}= 0;		 #Change
        $databaseLogsBajados{$cp3a} = $entry;                      # Set

}
#set to a boolean value to control whether hash keys are dumped in sorted order
print "CONTENIDO BBDD \%databaseLogsBajados:\n";
$Data::Dumper::Sortkeys = 1;
print Data::Dumper->Dump([\%databaseLogsBajados]);
close FILE;
}


sub borrarAntiguosLogsBajados
{
my ($grupoCP3A,$numDiasMaxEnBBDDdeLogs)=@_;

foreach my $cp3a (sort keys %databaseLogsBajados) {

	#Obtengo fichero log más reciente:
	my $lastdownloadedlogfile;
	#foreach my $key (reverse sort keys %{$entry}) 
	foreach my $key (reverse sort keys %{$databaseLogsBajados{$cp3a}}) 
	{
     	 	$lastdownloadedlogfile = $key;
		last; #Salgo del foreach en el primer loop ya que sólo necesito obtener el key más reciente
    	}	
	# Obtengo fecha del ultimo fichero log bajado:
	my $logfile = $lastdownloadedlogfile;
	my ($lastlogdate) = ($logfile =~ /cleaner_(\d{8})xx.log/);
	# $lastlogdate es por ejemplo "20060328"	

	#Elimino de la bbdd de ese cp3a todos los ficheros log registrados anteriormente:
	foreach my $fileInBddToRemove (sort keys %{$databaseLogsBajados{$cp3a}}) 
	{
		my $logfile2 = $fileInBddToRemove;
		my ($year,$month,$day) = ($logfile2 =~ /cleaner_(\d{4})(\d{2})(\d{2})xx.log/);	
		my ($year2,$month2,$day2) = Add_Delta_Days($year,$month,$day,$numDiasMaxEnBBDDdeLogs);
		my $var = sprintf "%4d%02d%02d",$year2,$month2,$day2;		
		if ($var < $lastlogdate)
		{# Borrar ese fich log de la BBDD porque es más antiguo en $numDiasMaxEnBBDDdeLogs que el último
		#log registrado	
		print  "Eliminado de la BBDD el fichero $fileInBddToRemove del CP3A $cp3a en el grupo $grupoCP3A por antiguedad\n";
		my $hash_ref = $databaseLogsBajados{$cp3a};     # Get
		delete($hash_ref->{$fileInBddToRemove});	#Change
       		$databaseLogsBajados{$cp3a} = $hash_ref;        # Set
		}
	}
}	
}


sub listarCp3aSinLogDeUnaFechaRegistradoEnBBDD
{
# Obtiene el listado de CP3A de los que se han bajado logs rotados en una determinada fecha
my ($fecha)=@_;
my @listOfCp3a;

foreach my $cp3a (sort keys %databaseLogsBajados) {

	if (!(exists($databaseLogsBajados{$cp3a}{"cleaner_".$fecha."xx.log"})))
	{
		push(@listOfCp3a,$cp3a);
	}
}
return @listOfCp3a;
}


sub bajarLogsGrupoCP3ARotadosEnUnaFecha
{
my ($grupoCP3A,$yearToDownload,$monthToDownload,$dayToDownload)=@_;
#NOTA: "%databaseLogsBajados" NO ES UN HASH, sino una referencia a un hash con MLDBM obtenieda con "tie"
#Algoritmo: Bajar log rotados en la fecha especificada

my ($year,$month,$day,$hour,$min,$sec) = Today_and_Now([$gmt]);
# Añado a la fecha el offset con GMT (1 ó 2 horas según mes del año):
($year,$month,$day, $hour,$min,$sec) = Add_Delta_YMDHMS($year,$month,$day, $hour,$min,$sec,$D_y,$D_m,$D_d, $Dh,$Dm,$Ds);
printf  "%s\n","-"x80;
printf "%4d-%02d-%02d %02d:%02d:%02d INTENTANDO BAJAR LOGS DEL GRUPO $grupoCP3A\n",$year,$month,$day,$hour,$min,$sec;
printf  "%s\n","-"x80;

foreach my $cp3a (sort keys %databaseLogsBajados) {
      		
		($year,$month,$day, $hour,$min,$sec) = Today_and_Now([$gmt]);
		($year,$month,$day, $hour,$min,$sec) = Add_Delta_YMDHMS($year,$month,$day, $hour,$min,$sec,$D_y,$D_m,$D_d, $Dh,$Dm,$Ds);
		my $fechayhoraAccesoCP3A = sprintf "%4d-%02d-%02d %02d:%02d:%02d",$year,$month,$day,$hour,$min,$sec;
		print "$fechayhoraAccesoCP3A INTENTANDO CP3A $cp3a...\n";
		 my $logurlbase = "https://$cp3a/admin/logsSystem.html?x=system.SystemArchiveLogDownLoad&id=cleaner_";
		 my $login = "https://$cp3a/admin/admin.html";	 

		my $date = sprintf "%4d%02d%02d",$yearToDownload,$monthToDownload,$dayToDownload;
		if (exists($databaseLogsBajados{$cp3a}{"cleaner_".$date."xx.log"}))
		{
		print "Log cleaner_".$date."xx.log ya ha sido descargado anteriormente. No se intentará obtener de nuevo para evitar un duplicado de datos\n";
		}
		else
		{
		# No se ha bajado aún el log rotado en esa fecha para el cp3a siendo tratado. Se procede a bajar el log
		# Creamos el ua
		
		# KEEP_ALIVE del ua: 
		# The side that initiates the close of the connection will end up with the TIME_WAIT. In normal HTTP/1.0 mode, the sever will have to close the HTTP connection to indicate end-of-content for each response it sends. In this case the server ends up with a TIME_WAIT for each response. With HTTP/1.1 persistent connections (what you get with the keep_alive option to LWP) it will normally be the client side that close the connection when it is done. In this case the client host end up with the TIME_WAIT.
		
		#If the keep_alive option is passed in, then a LWP::ConnCache is set up (see conn_cache() method
		# below). The keep_alive value is a number and is passed on as the total_capacity for the connection
		# cache. The keep_alive option also has the effect of loading and enabling the new experimental
		# HTTP/1.1 protocol module.
		
		# Get/sets the number of connection that will be cached. Connections will start to be dropped when
		# this limit is reached. If set to 0, then all connections are immediately dropped. If set to undef,
		# then there is no limit.

		 my $ua = LWP::UserAgent->new(keep_alive => 1);
		 $ua->cookie_jar(HTTP::Cookies->new(file => "cookies.txt", autosave => 1));
		 $ua->max_size( $maxBytesOfCp3aLogFile );
		 $ua->timeout( $timeoutInSecsOfHttpGet );
		 $ua->agent('Mozilla/5.0');
		 push @{ $ua->requests_redirectable }, 'POST';
		 my %form = ( 
		 		 		 action => 'login',
		 		 		 username => 'administrator',
		 		 		 password => 'password'
		 );
		 # hacemos el login
		 print  "Intentando Login... ";
		 my $res = $ua->post ($login, \%form);

		 if ($res->is_success) {
			printf "Login Correcto. Versión de CP3A: %s\n",$res->title( ) || "(no title)";
			#TRATAR UN SOLO CP3A
			&bajarLogsRotadosEnUnaFecha($cp3a,$grupoCP3A,$fechayhoraAccesoCP3A,$logurlbase,$ua,$yearToDownload,$monthToDownload,$dayToDownload);
		}
		else {
		 	print "ACCESO INCORRECTO! No se ha podido autenticar el acceso en la URL $login: \n"; 
			print "Error obtenido: ".$res->status_line."\n";
		 }
		}
		printf  "%s\n","-"x80;
}

}


sub bajarLogsRotadosEnUnaFecha
{
my ($cp3a,$grupoCP3A,$fechayhoraAccesoCP3A,$logurlbase,$ua,$year,$month,$day)=@_;	
my $lognumber = 0; #Inicializo Número de log
my $numMaxOfLogNumber = 3; # Número máximo del índice de ficheros log
my $tempfile = "$pathCp3aLogs/tempfile.log";
my $tempfile2 = "$pathCp3aLogs/tempfile2.log";

# Algoritmo: Trata de bajar logs rotados ayer con fecha de ayer en el nombre del fichero

# Borro fichero temporal si existe:
if (-e $tempfile) { unlink($tempfile); }

my $date = sprintf "%4d%02d%02d",$year,$month,$day;	
my $dateWithDashes = sprintf "%4d-%02d-%02d",$year,$month,$day;
my $logencontrado = 0;
my ($resultadoHTTPget,$downloadedfile,$cp3alogFileSize);

print "Intentando bajar log rotado el dia $dateWithDashes del CP3A $cp3a del grupo $grupoCP3A...\n";

while ((! $logencontrado) && ($lognumber <= $numMaxOfLogNumber))
{	
	# Solo bajo logs que hayan rotado antes que el día de ejecución del script
	my $stringlognumber = sprintf "%02d",$lognumber;
	my $datetag = "$date$stringlognumber";
	my $logurl = "$logurlbase$datetag.log";
	print  "INTENTANDO DESCARGAR $logurl\n";
	my $req = HTTP::Request->new(GET => $logurl);
	#my $response = $ua->request($req); #para obtener contenido en memoria
	#When you're requesting a large (or at least potentially large) document, a problem with the normal way of using the request methods (like $response = $ua->get($url)) is that the response object in memory will have to hold the whole document -- in memory. If the response is a thirty megabyte file, this is likely to be quite an imposition on this process's memory usage.
	#A notable alternative is to have LWP save the content to a file on disk, instead of saving it up in memory. This is the syntax to use:	
	my $response = $ua->request($req,$tempfile); 
	# Vuelco el log descargado a un fichero ($tempfile) en lugar de usar memoria

	if ($response->is_error( )) {
   		printf "$fechayhoraAccesoCP3A ERROR EN LA RESPUESTA! Código de respuesta de HTTP GET $cp3a es: %s\n", $response->status_line;
		push (@listaCp3aInaccesibles,$cp3a);
		if (-e $tempfile) { unlink($tempfile); }
		# Envío mail de alerta
		my $subject = "ERROR en código de respuesta de HTTP GET de $cp3a"; 
		my $body = sprintf "Se ha ejecutado \"$pathScript/getCP3Aviruscleanerlog.pl -downloadlogs $grupoCP3A\"\n\n$fechayhoraAccesoCP3A =>\n- ERROR EN LA RESPUESTA! Codigo de respuesta de HTTP GET $cp3a es: %s\n- URL que ha fallado: $logurl\n", $response->status_line;
		my $mailer = new Mail::Mailer 'smtp', Server => $mailserver;
		$mailer->open({ From    => $from_mail_address,
                                To      => @list_to_mail_addresses,
                                Subject => $subject,
                              })
		or die "Can't open: $!\n";
		print $mailer $body;
		$mailer->close( );
  	}
	elsif ($response->content_type( ) eq "save/application")
	{
	# Si el fichero log no existe la respuesta es un error en HTML ($response->content_type eq "text/html")
	# Si el fichero log existe entro en este "if".
		printf "- Log encontrado y descargado. Código de respuesta de HTTP GET: %s, Content Type: %s\n",$response->status_line,$response->content_type;
		# Calculo tamaño del fichero bajado:
		$cp3alogFileSize = -s $tempfile;
		 if ($cp3alogFileSize)
		{	
			# Si existe y tiene tamaño > 0 bytes es que es un fichero log de viruscleaner
			$logencontrado = 1; #Log encontrado, no debo seguir buscando
			#$numLogsBajados++;
			($downloadedfile) = ($logurl =~ /https.*(cleaner_\d{10}.log)/);
			# $logurl puede ser por ejemplo:
			#https://cpysmtpmx1.adm.correo/admin/logsSystem.html?x=system.SystemArchiveLogDownLoad&id=cleaner_2006033100.log
			print  "- Bajado con éxito $downloadedfile rotado el dia $dateWithDashes del CP3A $cp3a ($cp3alogFileSize bytes)\n";	
		}
		else
		{
			unlink($tempfile);
		}
	}
	else
	{
		# Borro fichero temporal porque los datos que hay no son para analizar:
		unlink($tempfile);
	}
	#Incremento el número del fich log con fecha X para bajar el siguiente LOG con misma fecha:
	$lognumber++;
}

if (-e $tempfile) 
{		
# Si existe un $tempfile es que tengo datos que tratar

	print "- Tratando log $downloadedfile rotado a las 00:00 h con registros de virus filtrados el $dateWithDashes\n";
	#TRATO LOS LOGS
	&juntarLogsDelMismoGrupoCP3A($grupoCP3A,$tempfile,$dateWithDashes);
	# Borro fichero temporal:
	unlink($tempfile);
	
	#Añado log bajado y tratado en la bbdd para poder consultar a posteriori qué logs se han podido bajar
	# por cada CP3A (no es necesario, pero está bien poder disponer de ésta información fácilmente):

	my $entry = $databaseLogsBajados{$cp3a};                   # Get
	$entry->{"cleaner_".$date."xx.log"} = $cp3alogFileSize;		#Change
       	$databaseLogsBajados{$cp3a} = $entry;                      # Set
	
	print  "- Fichero cleaner_"."$date"."xx.log (xx = 00,01,02, etc) registrado en BBDD de logs bajados de $cp3a\n";
}
}


sub juntarLogsDelMismoGrupoCP3A
{
my ($grupoCP3A,$tempfile,$dateWithDashes) = @_ ;

my $data_logfile = "$pathCp3aLogs/viruscleaner_all_$grupoCP3A\_$dateWithDashes.log";
`grep $dateWithDashes $tempfile >> $data_logfile`;
}



sub analizarFicherosLogExistentes
{
my $groupCP3A = shift;
# Globbing: gets all the files in the current directory, alphabetically sorted
my @log_files = glob "$pathCp3aLogs/viruscleaner_all_$groupCP3A\_*.log";
my @newfiles; # Lista con los nuevos ficheros .csv que se van a generar
my ($year,$month,$day,$hour,$min,$sec) = Today_and_Now([$gmt]);
# Añado a la fecha el offset con GMT (1 ó 2 horas según mes del año):
($year,$month,$day,$hour,$min,$sec) = Add_Delta_YMDHMS($year,$month,$day, $hour,$min,$sec,$D_y,$D_m,$D_d, $Dh,$Dm,$Ds);

printf  "%s\n","-"x80;
printf "%4d-%02d-%02d %02d:%02d:%02d INTENTANDO ANALIZAR LOGS DEL GRUPO $groupCP3A\n", $year,$month,$day,$hour,$min,$sec;
printf  "%s\n","-"x80;

foreach my $fileitem (@log_files)
{
	my ($year1,$month1,$day1) = ($fileitem =~ /.+viruscleaner_all_$groupCP3A\_(\d\d\d\d)-(\d\d)-(\d\d)\.log\b/);
        my $fileDate = sprintf "%4d-%02d-%02d",$year1,$month1,$day1;
	# Obtengo el análisis estadístico del fichero global
	print  "- Fichero log global $fileitem con registros del día $fileDate va a ser analizado y despues eliminado\n";
	my $outputfile = &analizarFicheroLog($fileitem);
        # Una vez analizado elimino el fichero log global:
	unlink($fileitem);
	if ($outputfile ne "ficheroYaExiste")
	{
	print "- Resultado estadístico del día $fileDate para el grupo $groupCP3A se puede encontrar en $outputfile\n";
	push(@newfiles,$outputfile);
	}
}
return @newfiles;	# Devuelvo path de los nuevos ficheros .csv con estadísticas
}


sub analizarFicheroLog
{
my $logfile = shift;
my ($type,$name);
my (%virustype,%virusname);
my $numberofviruses = 0;
my $csvline;

open (FH,"<",$logfile) or die "$fechayhoraInicioEjecucionScript Can't open log file: $! \n";

my ($CP3Agroup) = ($logfile =~ /.*viruscleaner_all_(\D+)_.*/);
my ($year,$month,$day) = ($logfile =~ /.*(\d\d\d\d)-(\d\d)-(\d\d)\D+/);

my $outputfile = "$pathresultadoestadisticas/estadisticas-cp3a-viruscleaner-$CP3Agroup-$year$month$day.csv";

if (-e $outputfile) 
{
print "- ERROR!: Ya existe un fichero estadístico $outputfile generado anteriormente!!! -> NO SE ANALIZARÁ DE NUEVO EL LOG CON LOS NUEVOS DATOS\n";
$outputfile = "ficheroYaExiste";
}
else
{
open OUTPUTDATA, ">$outputfile" or die "$fechayhoraInicioEjecucionScript can't open $outputfile $!";

while (<FH>) {

if (($type,$name)= m/.*type\s+(\w+-\w+)\.(\S+)/o  )
{
        ($year,$month,$day) = ($logfile =~ /.*(\d\d\d\d)-(\d\d)-(\d\d)\D+/);
        $month--;
        $virustype{ $type }++;
        $virusname{ $name }{'COUNT'}++;
        $virusname{ $name }{'TYPE'} = $type;
        $numberofviruses++;
}
}
foreach my $virus (reverse sort {$virusname{$a}{'COUNT'} <=> $virusname{$b}{'COUNT'}} keys %virusname){
$csvline = "$virus|$virusname{$virus}{'COUNT'}|$virusname{$virus}{'TYPE'}";
print OUTPUTDATA "$csvline\n";
}
delete @virustype{keys %virustype};
delete @virusname{keys %virusname};
close (OUTPUTDATA);
}
return $outputfile;
}



sub rotatelogs ($$) {
  my($file,$howmany) = @_;
  my($cur);

# rotate the named log file and archive $howmany old versions.  eg,
#   rotate("foo",3);
# will move foo -> foo.0 -> foo.1 -> foo.2 -> foo.3
# and remove old foo.3, then create empty foo.

  return if ($howmany < 0);

  unlink ("$file.$howmany","$file.$howmany.gz"); # remove topmost one.

  for ($cur = $howmany; $cur > 0; $cur--) {
    my $prev = $cur - 1;
    rename("$file.$prev","$file.$cur") if (-f "$file.$prev");
    rename("$file.$prev.gz","$file.$cur.gz") if (-f "$file.$prev.gz");
  }

  rename("$file","$file.0");    # move original one

  # create the new one!
  my $fh = new IO::File $file, O_WRONLY|O_CREAT, 0644;
  $fh->close();
}
