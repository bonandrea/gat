# chat_client.py
# -*- coding: iso-8859-15 -*-

'''
========================================================================
### segnali INVIATI al server:
entrambe le modalità: 	raspnod 
modalità grafo:  	addedge - remedge
modalità albero:	aggnodo - rimnodo 

### segnali RICEVUTI dal server (X=numero pin):
modalità grafo:  	Added a node to the graph 
			grafook - riprist - blinka:COLORE
modalità albero: 	aggnodo - nonodo - rimnodo 
			error - resetpl - guidato
			
========================================================================
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
LED_COUNT   = 30      # Number of LED pixels.
LED_PIN     = 18      # GPIO pin connected to the pixels (must support PWM!).
##### in realta strip posizionata su pin 12
LED_FREQ_HZ = 800000  # LED signal frequency in hertz (usually 800khz)
LED_DMA     = 5       # DMA channel to use for generating signal (try 5)
LED_INVERT  = False   # True to invert the signal (when using NPN transistor level shift)import time

gpio.setmode(gpio.BOARD)  	# Numerazione board
gpio.setwarnings(False)

# variabili numero pin
inpbutton=3	# pulsante nodo-albero			GPIO02
outbutton=5	# pulsante nodo-albero a HIGH		GPIO03
out3=19		# output edge-grafo a HIGH		GPIO10
inp3=21		# input edge-grafo, legge out3		GPIO09
out2=16		# output edge-arco a HIGH		GPIO23
inp2=18		# input edge-grafo, legge out2		GPIO24
out4=31		# output edge-grafo a HIGH		GPIO06
inp4=33		# input edge-grafo, legge out4		GPIO13
inp1=38		# input edge-grafo, legge out3		GPIO20
out1=40		# output edge-grafo a HIGH 		GPIO21
led1=16		# output-led a HIGH			GPIO23

# setup dei led e button collegati ai pin della board
#gpio.setup(inpbutton, gpio.IN, pull_up_down=gpio.PUD_DOWN)	# GPIO02 input, button, abilita pull-down, add-remove node
gpio.setup(inpbutton, gpio.IN, pull_up_down=gpio.PUD_UP)	# GPIO17 input, button, abilita pull-down, add-remove node
gpio.setup(outbutton, gpio.OUT)					# GPIO27 output, button sempre a HIGH
gpio.setup(inp1, gpio.IN, pull_up_down=gpio.PUD_DOWN)		# GPIO20 input, edge: legge il gpio21
gpio.setup(out1, gpio.OUT)					# GPIO21 output, edge: messo a HIGH
gpio.setup(inp2, gpio.IN, pull_up_down=gpio.PUD_DOWN)		# GPIO24 input, edge: legge il gpio25
gpio.setup(out2, gpio.OUT)					# GPIO23 output, edge: messo a HIGH
gpio.setup(inp3, gpio.IN, pull_up_down=gpio.PUD_DOWN)		# GPIO09 input, edge: legge il gpio10
gpio.setup(out3, gpio.OUT)					# GPIO10 output, edge: messo a HIGH
gpio.setup(inp4, gpio.IN, pull_up_down=gpio.PUD_DOWN)		# GPIO13 input, edge: legge il gpio13
gpio.setup(out4, gpio.OUT)					# GPIO06 output, edge: messo a HIGH
gpio.setup(led1, gpio.OUT)					# GPIO23 output, led messo a HIGH

gpio.output(led1, 1)


#=================================================================
# funzione per registrre log del client
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
    path = './log-nodo'+str(nodo)+'.txt'
    fh = open(path, "a")
    fh.write(data)
    fh.write("\n")
    fh.close()

sessione = setupSession()			# faccio partire sessione per raccolta log

#========================================================
''' Define functions which animate LEDs in various ways. '''
#========================================================

# accendo solo il led scelto con il colore desiderato
def color(strip, led, color):
    strip.setPixelColor(led, color)
    strip.show()

# accende tutti i led della strip del colore scelto
def colorWipe(strip, color, wait_ms=50):
	"""Wipe color across display a pixel at a time."""
	for i in range(strip.numPixels()):
		strip.setPixelColor(i, color)
		strip.show()
		time.sleep(wait_ms/300.0) 	#era 100.0

# faccio blinkare led=numero-led-sulla-strip, color=coloreRGB, times=quante-volte
def blink(strip, led, color, times=3, wait_ms=50):		
	for i in range(0,times):
                strip.setPixelColor(led, color)		
                strip.show()
                time.sleep(wait_ms/100.0)
                strip.setPixelColor(led, Color(0,0,0))	
                strip.show()
                time.sleep(wait_ms/100.0)

# blinka i led in successione dal primo all'ultimo e ritorno
def superCar(strip,color,wait_ms=20):
	for i in range(strip.numPixels()):
		strip.setPixelColor(i, color)
		print("color Red Led "+str(i))
		strip.show()
		time.sleep(wait_ms/100.0)
		strip.setPixelColor(i, Color(0,0,0))
		strip.show()
		print("color NONE Led "+str(i))
		time.sleep(wait_ms/100.0)
	for i in reversed(range(strip.numPixels())):
		strip.setPixelColor(i, color)
		print("color Red Led "+str(i))
		strip.show()
		time.sleep(wait_ms/100.0)
		strip.setPixelColor(i, Color(0,0,0))
		strip.show()
		print("color NONE Led "+str(i))
		time.sleep(wait_ms/100.0)

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
strip = Adafruit_NeoPixel(LED_COUNT, LED_PIN, LED_FREQ_HZ, LED_DMA, LED_INVERT)
strip.begin()

host = sys.argv[1]
port = int(sys.argv[2])
s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
nodo = socket.gethostname()				# ritorna il nome del raspberry, da impostare con tre numeri

#=======================================================================
''' funzioni per gestione segnali led '''
#=======================================================================

# accendere led di determinato colore se livello 1 determinato pin
def led(inp, ld, col):
    if gpio.input(inp):					
	color(strip, ld, col)
	strip.show()

# accendere tutte le luci

#=======================================================================
''' funzioni per aggiungere-rimuovere nodi e segnalare archi al grafo '''
#=======================================================================

# per evitare confusione invio data, 
# se arriva dal server 'riprist' --> mette la mod_albero=1
mod_albero=0

invio = random.random()

# Variabili per i pulsanti
pulsantenodo = False          		# Memoria lampeggio attivo
arcouno = False
arcodue = False

# Funzione per accendere il nodo-ALBERO con pulsante (metodo pulsante)
def attiva_nodo(pin):
    global pulsantenodo            	# Importa la variabile
    scriviLog("Pulsantearco prima di schiacciare bottone: " +str(pulsantenodo))
    print pulsantenodo
    #if mod_albero==1:
    if pulsantenodo:               	# Se pulsantenodo è True
	pulsantenodo = False       	# lo metto a False
	s.send('rimnodo' + str(nodo) +str(pin))
	scriviLog("Albero: rimosso dall'albero il nodo--> " +str(nodo))
    else:                       			
	pulsantenodo = True		# metto pulsantenodo a True
	s.send('aggnodo' + str(nodo) +str(pin))
	scriviLog("Albero: aggiunto all'albero il nodo--> " +str(nodo))
  
#====================================================

pin_values = {inp1:0,inp2:0,inp3:0,inp4:0}		# all'inizio {inp: 0} , dopo {inp: 1}
gpio.output(out1,1)
gpio.output(out2,1)
gpio.output(out3,1)
gpio.output(out4,1)

# attivazione arco-grafo - funzione riscritta con Rino (metodo lettura-pin)
def arco_grafo(pin):
    
    read_val = gpio.input(pin)		# legge il valore di pin input
					# pin possibibli 32=inp1 | 18=inp2 | 29=inp3 | 37=inp4
    if(read_val!=pin_values[pin]):
        if (read_val==1):
	    s.send('addedge' + str(nodo) + str(pin))		# addedgeA36 dove: A=nodo 36=pin
	    scriviLog("Grafo:  aggiunto parte-arco al nodo " +str(nodo) +'-' +str(pin))
	    pin_values[pin]=1
	    
        elif(read_val==0):
	    s.send('remedge' + str(nodo) + str(pin))
	    scriviLog("Grafo:  rimosso parte-arco dal nodo " +str(nodo) +'-' +str(pin))
	    pin_values[pin]=0
	    
# Interrupt: inseriamo un evento che causera la chiamata della funzione "attiva_nodo"
# ogni volta che viene rilevato un fronte di salita sul GPIObutton e sul GPIOinp
# funzione arco_albero = funzione gestione-arco | funzione edgedue = funzione pulsante
# gpio.add_event_detect(inpbutton, gpio.BOTH, callback=arco_albero, bouncetime=100) # usato con lo slider 
gpio.add_event_detect(inpbutton, gpio.BOTH, callback=attiva_nodo, bouncetime=100) # gpio.RISING
gpio.add_event_detect(inp1, gpio.BOTH, callback=arco_grafo) #bouncetime=500)
gpio.add_event_detect(inp2, gpio.BOTH, callback=arco_grafo) #bouncetime=500)
gpio.add_event_detect(inp3, gpio.BOTH, callback=arco_grafo) #bouncetime=500)
gpio.add_event_detect(inp4, gpio.BOTH, callback=arco_grafo) #bouncetime=500)

print("Pronto!")

# funzione per scrivere log
def scriviLog(logmessaggio):
    linealog= str(sessione) +', ' +(logmessaggio) +' | ' +str(datetime.datetime.now())
    storeLog(linealog)

#=======================================================================
''' azioni da svolgere in seguito ai messaggi inviati dal server al nodo '''
#=======================================================================

# Grafo e Albero: aggiunta e rimozione arco
def arrivodaserver(messaggio, a,b,c):
    scriviLog("Riceve: ricevuto comando ------> " +str(messaggio))
    colorWipe(strip, Color(a,b,c))
    #strip.show()
			
#=======================================================================
''' funzione principale '''
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
    
    sys.stdout.write('[Nodo]'); sys.stdout.flush()
    print 'Identificativo del nodo = ',nodo             	
    s.send('addnode' + str(nodo))
    scriviLog("Grafo:  aggiunto nodo " +str(nodo))
    
    
    try:
        while 1:
            socket_list = [sys.stdin, s]
            #nodo = socket.gethostname()
            #print nodo

            # Get the list sockets which are readable
            read_sockets, write_sockets, error_sockets = select.select(socket_list , [], [])
            for sock in read_sockets:			# ricezione msg dal server
                if sock == s:
                    arrivo = sock.recv(4096)		# incoming message from remote server, s
		    
                    if not arrivo:
                        print '\nDisconnected from chat server'
                        sys.exit()
		    else :
			sys.stdout.write(arrivo)
			if arrivo == 'Added a node to the graph':	# arriva testo conferma dal server
			    colorWipe(strip, Color(255,255,255), wait_ms=50)
			    strip.show()
		    
			elif arrivo == 'Removed node from the graph':
			    gpio.output(blue,0)
			    
			elif arrivo == 'cisei':
			    s.send('iamlive ' +str(nodo))
			    
			#===============================================
			# segnalazioni del pulsante conferma
			#===============================================
						
			elif arrivo == 'grafook':		
			    colorWipe(strip, Color(255,0,0))
			    strip.show()
			    scriviLog('Grafo:  il grafo risulta connesso       ')
			    				
			elif arrivo == 'brown':	
			    theaterChase(strip, Color(102,0,51), wait_ms=50, iterations=10)
			    strip.show()
			    colorWipe(strip, Color(102,0,51))
			    strip.show()
			    scriviLog('Errore: albero non ricoprente, brown    ')
			    
			elif arrivo == 'giallo':		
			    theaterChase(strip, Color(255,255,0), wait_ms=50, iterations=10)
			    strip.show()
			    colorWipe(strip, Color(255,255,0))
			    strip.show()
			    scriviLog('Errore: albero non ricoprente, giallo   ')
			    
			elif arrivo == 'purple':		
			    theaterChase(strip, Color(5,237,63), wait_ms=50, iterations=10)
			    strip.show()
			    colorWipe(strip, Color(5,237,63))
			    strip.show()
			    scriviLog('Errore: albero non ricoprente, purple   ')
			    
			elif arrivo == 'arancio':		
			    theaterChase(strip, Color(51,242,29), wait_ms=50, iterations=10)
			    strip.show()
			    colorWipe(strip, Color(51,242,29))
			    strip.show()
			    scriviLog('Errore: albero non ricoprente, arancio  ')
			    
			elif arrivo == 'viola':		
			    theaterChase(strip, Color(154,71,213), wait_ms=50, iterations=10)
			    strip.show()
			    colorWipe(strip, Color(154,71,213))
			    strip.show()
			    scriviLog('Errore: albero non ricoprente, viola    ')
			    
			elif arrivo == 'azure':		
			    theaterChase(strip, Color(217,33,147), wait_ms=50, iterations=10)
			    strip.show()
			    colorWipe(strip, Color(217,33,147))
			    strip.show()
			    scriviLog('Errore: albero non ricoprente, nero     ')
			    
			elif arrivo == 'riprist':
			    global mod_albero
			    mod_albero=1
			    scriviLog('Server: CAMBIO di SCENARIO              ')
			    colorWipe(strip, Color(255,255,255))
			    strip.show()
			    
			elif arrivo == 'rialber':
			    scriviLog('Albero: ripristina albero creato        ')
			    colorWipe(strip, Color(0,0,255))
			    
			elif arrivo == 'resetpl':
			    global pulsantenodo
			    pulsantenodo = False
			    colorWipe(strip, Color(255,255,255))
			    scriviLog('Tornato a modalita grafo, reset pulsante')
			    			    
			#===============================================
			# segnalazioni per creazione ALBERO
			#===============================================
			
			elif arrivo == 'aggnodo':
			    arrivodaserver(arrivo, 0,0,255)
			    
			elif arrivo == 'nonodo':	
			    theaterChase(strip, Color(0,255,0), wait_ms=50, iterations=10)
			    arrivodaserver(arrivo, 0,255,0)
			    
			elif arrivo == 'rimnodo':
			    arrivodaserver(arrivo, 255,255,255)
			
			elif arrivo == 'guidato':			# segnala giusto arco secondo Prim
			    theaterChase(strip, Color(0,0,255), wait_ms=50, iterations=7)
			    strip.show()
			
			else:
			    scriviLog('Non arrivato nessun messaggio dal server ')
			    
    except KeyboardInterrupt:
        s.send('Chiusura del nodo' + str(nodo))
        gpio.cleanup()
	reset(strip)

        
if __name__ == "__main__":

    sys.exit(chat_client())
