# chat_client.py
# -*- coding: iso-8859-15 -*-

'''
========================================================================
##### segnali INVIATI al server: 
 con ritardo perche devono arrivare prima quelli del nodo
 Grafo:  rasparc - edgeadd - edgerem
 Albero: arcoagg - arcorim

##### segnali RICEVUTI dal server:
 Grafo:	 egdeadd - edgerem - resetpl
 Albero: arcoagg - arcorim - guidato
	 error - grafook - riprist - blinka:COLORE - resetpl
=======================================================================
'''

import time
import datetime
import sys, socket, select
import random
import os

# from gpiozero import LED, Button
import RPi.GPIO as gpio   	# Importa libreria GPIO

from neopixel import *

# LED strip configuration:
LED_COUNT   = 30      	# Number of LED pixels.
LED_PIN     = 18      	# GPI pin connected to the pixels (must support PWM!).
##### in realta strip posizionata su pin 12
LED_FREQ_HZ = 800000  	# LED signal frequency in hertz (usually 800khz)
LED_DMA     = 5       	# DMA channel to use for generating signal (try 5)
LED_BRIGHTNESS = 155  	# Set to 0 for darkest and 255 for brightest
LED_INVERT  = False   	# True to invert the signal (when using NPN transistor level shift)import time

gpio.setmode(gpio.BOARD)  	# Numerazione board
gpio.setwarnings(False)

# variabili numero pin
inpbutton=3	# pulsante arco-albero		GPIO02
outbutton=5	# pulsante arco-albero a HIGH	GPIO03
inp1=38		# pin che legge out1		GPIO20
out1=40		# pin a level a HIGH		GPIO21
inp2=32		# pin che legge out2		GPIO12
out2=36		# pin a level a HIGH		GPIO16
led1=29		# output-led			GPIO05
led2=31		# output-led			GPIO06
led3=33		# output-led			GPIO13
led4=35		# output-led			GPIO19
led5=37		# output-led			GPIO26

# setup dei led e button collegati ai pin della board
gpio.setup(inpbutton, gpio.IN, pull_up_down=gpio.PUD_DOWN)	# GPIO02 input, button, abilita pull-down, add-remove node
gpio.setup(outbutton, gpio.OUT)					# GPIO03 output, button sempre a HIGH
gpio.setup(inp1, gpio.IN, pull_up_down=gpio.PUD_DOWN)		# GPIO20 legge il valore del pin edge1
gpio.setup(out1, gpio.OUT)					# GPIO21 output, sempre a HIGH
gpio.setup(inp2, gpio.IN, pull_up_down=gpio.PUD_DOWN)		# GPIO12 legge il valore del pin edge4
gpio.setup(out2, gpio.OUT)					# GPIO16 output, sempre a HIGH
gpio.setup(led1, gpio.OUT, initial=0)				# GPIO05 output, led messo a HIGH
gpio.setup(led2, gpio.OUT, initial=0)				# GPIO06 output, led messo a HIGH
gpio.setup(led3, gpio.OUT, initial=0)				# GPIO13 output, led messo a HIGH
gpio.setup(led4, gpio.OUT, initial=0)				# GPIO19 output, led messo a HIGH
gpio.setup(led5, gpio.OUT, initial=0)				# GPIO26 output, led messo a HIGH

#=================================================================
# funzione per registrare log del client
#=================================================================

global sessione

# apre sessione per scrivere i log
def setupSession():
    path = "./session.txt"
    if os.path.exists(path) == False:
        print("Creating Session file ")
        fh=open(path,"w")
        fh.writelines("1")
        fh.close()
        return 1
    else:
        print("Updating session.txt file ")
        fh=open(path,"r+")
        olduserid=fh.readline()
        userid = int(olduserid)+1
        fh.seek(0)
        fh.write(str(userid)+"\n")
        fh.close()
        return userid

# associata a funzione sopra per log azioni svolte
def storeLog(data):
    path = './log-arco'+str(nodo)+'.txt'
    fh = open(path, "a")
    fh.write(data)
    fh.write("\n")
    fh.close()

sessione = setupSession()			# faccio partire sessione per raccolta log

#========================================================
# Define functions which animate LEDs in various ways.
#========================================================

# accendo solo il led scelto con il colore desiderato
def color(strip, led, color):
    strip.setPixelColor(led, color)
    strip.show()

# accende tutti i led della strip del colore scelto
def colorWipe(strip, color, wait_ms=10):		#prima era wait_ms=50
	"""Wipe color across display a pixel at a time."""
	for i in range(strip.numPixels()):
		strip.setPixelColor(i, color)
		strip.show()
		time.sleep(wait_ms/500.0) # prima era 100

# faccio blinkare led=numero-led-sulla-strip, color=coloreRGB, times=quante-volte
def blink(strip, led, color,times=3, wait_ms=50):
	for i in range(0,times):
                strip.setPixelColor(led, color)
                strip.show()
                time.sleep(wait_ms/100.0)
                strip.setPixelColor(led, Color(0,0,0))
                strip.show()
                time.sleep(wait_ms/100.0)

# blinka i led in successione dal primo all'ultimo e ritorno
#def superCar(strip,color,wait_ms=20):
	#for i in range(strip.numPixels()):
		#strip.setPixelColor(i, color)
		#print("color Red Led "+str(i))
		#strip.show()
		#time.sleep(wait_ms/100.0)
		#strip.setPixelColor(i, Color(0,0,0))
		#strip.show()
		#print("color NONE Led "+str(i))
		#time.sleep(wait_ms/100.0)
	#for i in reversed(range(strip.numPixels())):
		#strip.setPixelColor(i, color)
		#print("color Red Led "+str(i))
		#strip.show()
		#time.sleep(wait_ms/100.0)
		#strip.setPixelColor(i, Color(0,0,0))
		#strip.show()
		#print("color NONE Led "+str(i))
		#time.sleep(wait_ms/100.0)

# alterna led pari e dispari con colori diversi
def colorPairOdd(strip, colorPair,colorOdd, wait_ms=50):
        """Wipe color across display a pixel at a time."""
        for i in range(strip.numPixels()):
		if(i%2==0):
                	strip.setPixelColor(i, colorPair)
		else:
                	strip.setPixelColor(i, colorOdd)
			
                strip.show()
                time.sleep(wait_ms/100.0)

def colorPair(strip, colorPair, wait_ms=50):
        """Wipe color across display a pixel at a time."""
        for i in range(strip.numPixels()):
		if(i%2==0):
                	strip.setPixelColor(i, colorPair)
			
                strip.show()
                time.sleep(wait_ms/500.0)


def theaterChase(strip, color, wait_ms=50, iterations=10):
	"""Movie theater light style chaser animation."""
	for j in range(iterations):
		for q in range(3):
			for i in range(0, strip.numPixels(), 3):
				strip.setPixelColor(i+q, color)
			strip.show()
			time.sleep(wait_ms/1000.0)
			for i in range(0, strip.numPixels(), 3):
				strip.setPixelColor(i+q, 0)

def reset(strip):
	for i in range(strip.numPixels()):
		strip.setPixelColor(i, Color(0,0,0))
		
	strip.show()	
	
# Create NeoPixel object with appropriate configuration.
# Intialize the library (must be called once before other functions).
# provando ad inserire LED_BRIGHTNESS, stripled non si spegne piu
strip = Adafruit_NeoPixel(LED_COUNT, LED_PIN, LED_FREQ_HZ, LED_DMA, LED_INVERT, LED_BRIGHTNESS)
strip.begin()

host = sys.argv[1]
port = int(sys.argv[2])
s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
nodo = socket.gethostname()				# ritorna il nome del raspberry, da impostare con tre numeri

# funzione per accendere led di determinato colore se livello 1 determinato pin
def led(inp, ld, col):
    if gpio.input(inp):					
	color(strip, ld, col)
	strip.show()


#=======================================================================
# funzioni per aggiungere-rimuovere archi al grafo e albero
#=======================================================================

invio = random.random()

# Variabili per i pulsanti
pulsantearco = False          		# Memoria lampeggio attivo

# Funzione per attivare arco-albero con il pulsante (metodo pulsante)
def arco_albero(pin):
    global pulsantearco            	# Importa la variabile
    print pulsantearco
    scriviLog("Pulsantearco prima di schiacciare bottone: " +str(pulsantearco))
    if pulsantearco:               	# Se pulsantenodo attivo
        pulsantearco = False       	# lo metto a False
	s.send('arcorim' + str(nodo))
	scriviLog("Albero: disattivato l'arco --> " +str(nodo))
    else:                       			
        pulsantearco = True
        s.send('arcoagg' + str(nodo) +str(pin))
	scriviLog("Albero: attivato l'arco -----> " +str(nodo))
	
pin_values = {inp1:0,inp2:0}		# all'inizio {inp: 0} , dopo {inp: 1}
gpio.output(out1,1)
gpio.output(out2,1)

# attivazione arco-grafo (metodo lettura-pin)
def arco_grafo(pin):
    
    read_val = gpio.input(pin)		# legge il valore di pin input: 32=inp1, 37=inp2
    
    if(read_val!=pin_values[pin]):
        if (read_val==1):
	    time.sleep(0.6)
	    s.send('edgeadd' + str(nodo) + str(pin))		# edgeadda37 dove: a=arco 37=pin
	    scriviLog("Grafo:  aggiunto parte-arco " +str(nodo))
	    pin_values[pin]=1
	    
        elif(read_val==0):
	    time.sleep(0.6)
	    s.send('edgerem' + str(nodo) + str(pin))
	    scriviLog("Grafo:  rimosso  parte-arco " +str(nodo))
	    pin_values[pin]=0

#====================================================
	   
# Interrupt: inseriamo un evento che causera la chiamata della funzione "cambia_stato"
# ogni volta che viene rilevato un fronte di salita sul GPIObutton e sul GPIOinp
gpio.add_event_detect(inpbutton, gpio.BOTH, callback=arco_albero, bouncetime=100) 
gpio.add_event_detect(inp1, gpio.BOTH, callback=arco_grafo) #bouncetime=200)		
gpio.add_event_detect(inp2, gpio.BOTH, callback=arco_grafo) #bouncetime=200)		

print("Pronto!")

# funzione per scrivere log
def scriviLog(logmessaggio):
    linealog= str(sessione) +', ' +(logmessaggio) +' | ' +str(datetime.datetime.now())
    storeLog(linealog)

#=======================================================================
# azioni da svolgere in seguito ai messaggi inviati dal server all'arco
#=======================================================================

# Grafo: aggiunta e rimozione arco
def grafodaserver(messaggio, a,b,c):
    scriviLog("Riceve: ricevuto comando  " +str(messaggio))
    colorWipe(strip, Color(a,b,c),)
    #strip.show()

def alberodaserver(messaggio, a,b,c):
    scriviLog("Riceve: ricevuto comando  " +str(messaggio))
    colorWipe(strip, Color(a,b,c),)
    #strip.show()

# Grafo e Albero: segnalazioni di errore, parallelo e selfloop
def erroridaserver(messaggio, inp, numero, a,b,c):
    scriviLog("Riceve: ricevuto comando  " +str(messaggio))
    while gpio.input(inp):
	blink(strip, numero, Color(a,b,c))
	strip.show()

# inserito variabile globale per fare in modo che vengono ignorati i cmd albero quando in modalità grafo
mod_albero=0        # modalità di partenza, costruzione grafo


#=======================================================================
# funzione principale
#=======================================================================

def chat_client():
    
    if(len(sys.argv) < 3) : 
        print 'Usage : python chat_client.py hostname port'
        sys.exit()
	
    # inizialemnte erano scritte qui
    #host = sys.argv[1]
    #port = int(sys.argv[2])
    #s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    #s.settimeout(2)
   
    # connect to remote host
    try :
        s.connect((host, port))
    except :
        print 'Unable to connect'
        sys.exit()
    
    sys.stdout.write('[Arco]'); sys.stdout.flush()
    print 'Identificativo del arco = ',nodo             	
    s.send('rasparc' + str(nodo))		# solo per inserire rasp-arco nella lista dei socket
    
    try:
        while 1:
            socket_list = [sys.stdin, s]
            # nodo = socket.gethostname()

            # Get the list sockets which are readable
            read_sockets, write_sockets, error_sockets = select.select(socket_list , [], [])
            # ricezione msg dal server
            for sock in read_sockets:
                if sock == s:
                    # incoming message from remote server, s
                    arrivo = sock.recv(4096)
		    #scriviLog("Arrivo: " +str(arrivo))
		    
                    if not arrivo:
                        print '\nDisconnected from chat server'
                        sys.exit()
		    else :
			sys.stdout.write(arrivo)
			if arrivo == 'cisei':
			    s.send('iamlive ' +str(nodo))
			    
			#===============================================
			# segnalazioni per creazione GRAFO e ALBERO
			#===============================================
			
			elif arrivo == 'albero':
			    reset(strip)
			    theaterChase(strip, Color(255,255,255), wait_ms=50, iterations=7)
			    strip.show()
			    color(strip, 3, Color(255,255,255))
			    color(strip, 9, Color(255,255,255))
			    #colorPair(strip, Color(255,255,255), wait_ms=50)
			
			elif arrivo == 'edgeadd':
			    reset(strip)
			    theaterChase(strip, Color(255,255,255), wait_ms=50, iterations=7)
			    strip.show()
			    color(strip, 3, Color(255,255,255))
			    color(strip, 9, Color(255,255,255))
			    #colorPair(strip, Color(255,255,255), wait_ms=50)
			    
			elif arrivo == 'edgerem':		
			    grafodaserver(arrivo, 0,0,0)

			elif arrivo == 'arcoagg':
			    alberodaserver(arrivo, 0,0,255)
			
			elif arrivo == 'arcorim':
			    reset(strip)
			    theaterChase(strip, Color(255,255,255), wait_ms=50, iterations=7)
			    strip.show()
			    color(strip, 3, Color(255,255,255))
			    color(strip, 9, Color(255,255,255))
			    #colorPair(strip, Color(255,255,255), wait_ms=50)
			    
			elif arrivo == 'error':				# viene creato selfloop o arco parallelo
			    theaterChase(strip, Color(0,255,0), wait_ms=50, iterations=10)
			    strip.show()
			    scriviLog("Riceve: ERROR:  azione sbagliata")
			    colorWipe(strip, Color(0,255,0))
			
			elif arrivo == 'guidato':			# segnala giusto arco secondo Prim
			    theaterChase(strip, Color(0,0,255), wait_ms=50, iterations=10)
			    strip.show()
			    scriviLog("Riceve: da attivare questo arco" )
			
			elif arrivo == '1':				# se arco ha peso 1 si accende un led
			    gpio.output(led1, 1)
			    scriviLog("Riceve: il peso dell'arco è --> " +str(arrivo))
			    
			elif arrivo == '2':				# se arco ha peso 2 si accendono due led
			    gpio.output(led1, 1)
			    gpio.output(led2, 1)
			    scriviLog("Riceve: il peso dell'arco è --> " +str(arrivo))
			    
			    
			elif arrivo == '3':				# se arco ha peso 3 si accendono tre led
			    gpio.output(led1, 1)
			    gpio.output(led2, 1)
			    gpio.output(led3, 1)
			    scriviLog("Riceve: il peso dell'arco è --> " +str(arrivo))
			    
			elif arrivo == '4':				# se arco ha peso 4 si accendono tre led
			    gpio.output(led1, 1)
			    gpio.output(led2, 1)
			    gpio.output(led3, 1)
			    gpio.output(led4, 1)
			    scriviLog("Riceve: il peso dell'arco è --> " +str(arrivo))
			
			elif arrivo == '5':				# se arco ha peso 5 si accendono tre led
			    gpio.output(led1, 1)
			    gpio.output(led2, 1)
			    gpio.output(led3, 1)
			    gpio.output(led4, 1)
			    gpio.output(led5, 1)
			    scriviLog("Riceve: il peso dell'arco è --> " +str(arrivo))
			    
			#===============================================
			# segnalazioni del pulsante conferma
			#===============================================
			    
			elif arrivo == 'grafook':		
			    grafodaserver(arrivo, 255,0,0)
			    scriviLog('Riceve: grafo connesso, tutto ok ')
			
			elif arrivo == 'riprist':
			    reset(strip)
			    theaterChase(strip, Color(255,255,255), wait_ms=50, iterations=7)
			    strip.show()
			    color(strip, 3, Color(255,255,255))
			    color(strip, 9, Color(255,255,255))
			    #colorPair(strip, Color(255,255,255), wait_ms=50)
			    scriviLog('Riceve: CAMBIO di SCENARIO       ')
			
			elif arrivo == 'resetpl':
			    global pulsantearco
			    pulsantearco = False
			    scriviLog('Riceve: reset scenario precedente')
			    reset(strip)
			    theaterChase(strip, Color(255,255,255), wait_ms=50, iterations=7)
			    strip.show()
			    color(strip, 3, Color(255,255,255))
			    color(strip, 9, Color(255,255,255))	
			    
			elif arrivo == 'brown':	
			    theaterChase(strip, Color(102,0,51), wait_ms=50, iterations=10)
			    strip.show()
			    colorWipe(strip, Color(102,0,51))
			    strip.show()
			    scriviLog('Errore: albero non ricoprente    ')
			    
			elif arrivo == 'giallo':		
			    theaterChase(strip, Color(255,255,0), wait_ms=50, iterations=10)
			    strip.show()
			    colorWipe(strip, Color(255,255,0))
			    strip.show()
			    scriviLog('Errore: albero non ricoprente    ')
			    
			elif arrivo == 'purple':		
			    theaterChase(strip, Color(5,237,63), wait_ms=50, iterations=10)
			    strip.show()
			    colorWipe(strip, Color(5,237,63))
			    strip.show()
			    scriviLog('Errore: albero non ricoprente    ')
			    
			elif arrivo == 'arancio':		
			    theaterChase(strip, Color(51,242,29), wait_ms=50, iterations=10)
			    strip.show()
			    colorWipe(strip, Color(51,242,29))
			    strip.show()
			    scriviLog('Errore: albero non ricoprente    ')
			    
			elif arrivo == 'viola':		
			    theaterChase(strip, Color(33,45,217), wait_ms=50, iterations=10)
			    strip.show()
			    colorWipe(strip, Color(33,45,217))
			    strip.show()
			    scriviLog('Errore: albero non ricoprente    ')
			    
			elif arrivo == 'azure':		
			    theaterChase(strip, Color(217,33,147), wait_ms=50, iterations=10)
			    strip.show()
			    colorWipe(strip, Color(217,33,147))
			    strip.show()
			    scriviLog('Errore: albero non ricoprente    ')
			    
			elif arrivo == 'rialber':
			    scriviLog('Errore: albero non ricoprente    ')
			    colorWipe(strip, Color(0,0,255))
			    strip.show()
			
			else:
			    pass
			    #scriviLog('Non arrivato nessun messaggio dal server ')
			    
    except KeyboardInterrupt:
        s.send('Chiusura del arco' + str(nodo))
        gpio.cleanup()
	reset(strip)

        
if __name__ == "__main__":

    sys.exit(chat_client())
