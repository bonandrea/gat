# chat_server.py
# -*- coding: iso-8859-15 -*-

import sys, socket, select
import networkx as nx
import matplotlib.pyplot as plot
import random
import datetime
import time
import os
import pygame as pg

# necessari per mst
from heapq import heappop, heappush
from itertools import count

from operator import itemgetter
from math import isnan
from networkx.algorithms import tree

from threading import Thread
import threading

HOST = ''
SOCKET_LIST = []
RECV_BUFFER = 8192  #4096
PORT = 9009


#=======================================================================

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
    path = "./log-grafo.txt"
    fh = open(path, "a")
    fh.write(data)
    fh.write("\n")
    fh.close()

# fa partire il suono quando finito il grafo
def play_music(music_file, volume=0.8):
    '''
    stream music with mixer.music module in a blocking manner
    this will stream the sound from disk while playing
    '''
    # set up the mixer
    freq = 44100     # audio CD quality
    bitsize = -16    # unsigned 16 bit
    channels = 2     # 1 is mono, 2 is stereo
    buffer = 2048    # number of samples (experiment to get best sound)
    pg.mixer.init(freq, bitsize, channels, buffer)
    # volume value 0.0 to 1.0
    pg.mixer.music.set_volume(volume)
    clock = pg.time.Clock()
    try:
        pg.mixer.music.load(music_file)
        print("Music file {} loaded!".format(music_file))
    except pg.error:
        print("File {} not found! ({})".format(music_file, pg.get_error()))
        return
    pg.mixer.music.play()
    while pg.mixer.music.get_busy():
        # check if playback has finished
        clock.tick(30)

sigrafo = "./Music/ok.mp3"
nografo = "./Music/no.mp3"
volume = 0.8            # optional volume 0 to 1.0

# per testare se sull'arco si accendono tutti i 5 led
def testLed():
    ar=scka[0]
    ar.send('5')

#=======================================================================
''' funzioni e liste usate per creazione del GRAFO (node e edge) '''
#=======================================================================

# viene creato grafo G 
L1 = []			# lista id nodes	# ['A', 'B', 0, 0, 0, 0, 0, 0, 0]
L2 = []			# lista id archi	# ['a', 'b', 'c', 'd']
nomearco={}		# lega id-arco (key) con nome-arco-dato-dai-nodi (value)    # {'a': 'CB', 'c': 'AC', 'b': 'AB'}
sck=[]			# lista socket da associare alla L1 all'arrivo dei nodi
scka=[]			# lista socket da associare alla L2 all'arrivo degli archi
L4 = [0,0,0]	# lista temp dei futuri edges che si collegano ad un nodes	# ['B29', 'A32']
temponodo=[]	# tempo arrivo dei cmd da parte del raspnodo	# [datetime.datetime(2017, 5, 3, 16, 17, 33, 952926)]
tempoarco=[]    # tempo arrivo dei cmd da parte del rasparco
tempopuls=[]    # tempo arrivo dei cmd da parte del pulsante-conferma
indirizzo={}	# legame idn con parametro 'addr'# {'A': ('192.168.0.3', 39080), 'B': ('192.168.0.4', 60964)}
# dizionario con associazione edge(key) e node(value) associati, quando creo selfloop              
# quando creo archi paralleli	{'D37': ['G37'], 'G32': ['D32'], 'D32': ['G32'], 'G37': ['D37']}
diz = {}        # {'A32': ['B18'], 'B18': ['A32']}


#=====================================================================
''' funzioni e liste usate per creazione dell'ALBERO (nodo e arco)
    variabile e funzioni indicati in italiano e\o aggiunta una a finale '''
#=====================================================================

# viene creato grafo A (l'albero ricoprente) e grafo C (temporaneo)

##### liste comuni ad entrambe le modalità costruzione albero ricoprente 
La1=[]		    # lista dei nodi che arrivano	# ['A', 'B', 'C'] 
La4=[]		    # lista temp futuri archi che si collegano al nodo	# ['B22', 'A36', 'a'] 
La2 = []        # lista degli archi attivati in creazione albero ['a', 'b']

##### liste per creare albero ricoprente seguendo sequenza "nodo-arco-nodo" adiacente
Lf1 = []	    # lista dei nodi frontiera dei nodi presenti in La1
az=['arco']		    # lista che conserva sequenza azioni nodo-arco-nodo-arco	# ['arco', 'nodo', 'arco']
rasparco=[]	    # lista per vedere se rasp-arco è stato attivato


#=====================================================================
''' funzioni e liste usate per creazione minimum spanning tree '''
#=====================================================================

# viene creato A.grafo dove si calcola lo mst + C.grafo temporaneo
lista_mst = []
archiciclo = []     # lista temporanea in cui vengono inseriti archi facenti parti del ciclo
nodiattivati = []   # nodi attivati durante la costruzione del mstAdiac, posso usare quelli in C.grafo
daattivare = []     # nodi da attivare secondo algoritmo Prim --> [(1, 0, 'H', 'B')]
nodiMstPrim = []    # successione nodi da attivare in modalita mstPrim e mstGuid--> ['A', 'H', 'C']
archiMstPrim = []   # successione archi da attivare in modalità mstPPrim e mstGuid --> ['a', 'd', 'c']

#=======================================================================
# salvare il grafo costruito
def salva_grafo(sal):
    path = ('./salva_grafo.txt')
    gr = open(path, "a")
    gr.write(sal)
    gr.write("\n")
    gr.close()

# salvare albero costruito
def salva_alb(salb):
    path = ('./salva_albero.txt')
    gr = open(path, "a")
    gr.write(salb)
    gr.write("\n")
    gr.close()

#===========================================================================
# algoritmo PRIM usato nella def tastiera_server per far vedere passo passo costruzione grafo
def prim_mst_edges(G, weight='weight', data=True):
    if G.is_directed():
        raise nx.NetworkXError(
            "Mimimum spanning tree not defined for directed graphs.")

    push = heappush
    pop = heappop

    nodes = G.nodes()
    c = count()

    while nodes:
        u = nodes.pop(0)				# mi da il primo nodo alfabetico e lo toglie(pop) 
        frontier = []					# lista peso nodi di frontiera
        visited = [u]					# lista dei nodi visitati
        # per archi che partono dal nodo visitato u=nodo visitato, v=nodi frontiera
        for u, v in G.edges(u):
            # inserisce (push) il valore "G[u][v].get('weight', 1), next(c), u, v)" in [frontier]
            push(frontier, (G[u][v].get(weight, 1), next(c), u, v))

        while frontier:
            W, _, u, v = pop(frontier)  # fornisce il valore piu basso di frontier e lo toglie (pop) 
            if v in visited:
                continue
            visited.append(v)
            nodes.remove(v)
            for v, w in G.edges(v):
                if not w in visited:
                    push(frontier, (G[v][w].get(weight, 1), next(c), v, w))
            if data:
                yield u, v, G[u][v]
            else:
                yield u, v

# somma pesi diversi archi
def branching_weight(G, attr='weight', default=1):
    #Returns the total weight of a branching.
    return sum(edge[2].get(attr, default) for edge in G.edges(data=True))

# trovo con a la somma dei pesi del grafoA = mst
listaPesiMst=[]
listaPesiAlb=[]
def sommaPesiMst():  
    mst=nx.prim_mst_edges(G, weight='weight', data=True)
    lista=list(mst)
    print lista
    lung=len(lista)
    i=0
    while i<lung:    
        peso = lista[i][2]['weight']    
        listaPesiMst.append(peso)
        i=i+1
    a=0
    for b in listaPesiMst:
        a=a+b 
    print a

def sommaPesiAlb():  
    mst=nx.prim_mst_edges(A, weight='weight', data=True)
    lista=list(mst)
    print lista
    lung=len(lista)
    i=0
    while i<lung:    
        peso = lista[i][2]['peso']    
        listaPesiAlb.append(peso)
        i=i+1
    a=0
    for b in listaPesiAlb:
        a=a+b 
    print a

# inserito variabile globale per fare in modo che vengono ignorati i cmd albero quando in modalità grafo
mod_albero=0        # modalità di partenza, costruzione grafo

#=======================================================================
# funzioni per le diverse modalità di costruzione albero e MST, lanciate da tastiera
#=======================================================================

grafo_docente=False
# funzione per inserimento grafo desiderato da insegnante
def insertGrafoIns():
    global grafo_docente
    grafo_docente=True
    with open('Dropbox/prototipo/codice/grafo.txt') as f:
        lines = f.readlines()
    myList = [line.strip().split() for line in lines]
    print myList
    H.add_weighted_edges_from(myList)

# invia segnale per passare a modalita albero secondo regola "nodo-arco-nodo adiacenti"
def modalitaSTprim():
    global mod_albero
    mod_albero=1
    print ('Costruzione albero: modalità Prim')
    print mod_albero
    #for nodi in G.nodes():
        #no=SOCKET_LIST[L1.index(nodi)]              # individuo socket riferito a quel nodo (label)
        #no.send("riprist")
        
    #for nds in G.nodes():
        #posiz=L1.index(nds)+1              # posizione della label nella lista
        #no=SOCKET_LIST[posiz]              # individuo socket riferito a quel nodo (label)
        #no.send("riprist")

# invia segnale per passare a modalita albero LIBERO
def modalitaSTlibera():
    global mod_albero
    mod_albero=2
    print 'Costruzione albero: modalità libera'
    print mod_albero
    #for nodi in G.nodes():
        #no=SOCKET_LIST[L1.index(nodi)]              # individuo socket riferito a quel nodo (label)
        #no.send("riprist")


# invia segnale per passare a modalita MST libera
def modalitaMSTfree():
    global mod_albero
    mod_albero=3
    print 'Costruzione minimum spanning tree'
    print mod_albero
    for nds in G.nodes():
        posiz=L1.index(nds)+1              # posizione della label nella lista
        no=SOCKET_LIST[posiz]              # individuo socket riferito a quel nodo (label)
        no.send("riprist")
    for a in L2:
        pos=L2.index(a)
        ar=scka[pos]
        peso= G[nomearco[a][0]][nomearco[a][1]]['weight']  # diz= G['A']['B'], trovo value di key con [0]['weight']
        print peso
        ar.send(str(peso))
        
# invia segnale per passare a modalita MST secondo regola "nodo-arco-nodo adiacenti"
def modalitaMSTadiacenti():
    global mod_albero
    mod_albero=4
    print 'Costruzione minimum spanning tree'
    print mod_albero
    for nds in G.nodes():
        posiz=L1.index(nds)+1              # posizione della label nella lista
        no=SOCKET_LIST[posiz]              # individuo socket riferito a quel nodo (label)
        no.send("riprist")
    for a in L2:
        pos=L2.index(a)
        ar=scka[pos]
        peso= G[nomearco[a][0]][nomearco[a][1]]['weight']  # diz= G['A']['B'], trovo value di key con [0]['weight']
        print peso
        ar.send(str(peso))
        
# invia segnale per passare a modalita MST secondo algortimo Prim
def modalitaMSTprim():
    global mod_albero
    mod_albero=5      
    print 'Costruzione minimum spanning tree'
    print mod_albero
    modalitaMST()

# invioa segnale per passare a modlaità secondo Prim guidata da oggetto
def modalitaMSTguid():
    global mod_albero
    mod_albero=6
    print 'Costruzione minimum spanning tree guidato'
    print mod_albero
    modalitaMST()
      
#funzione comune alle due modalità MST secondo Prim
def modalitaMST():    
    mstprim=list(nx.prim_mst_edges(G, weight='weight', data=True))  # [('A', 'B', {'arco': 'AB', 'rasparco': 'i', 'weight': 1}), ('A', 'D', {'arco': 'AD', 'rasparco': 'm', 'weight': 2}), ('B', 'C', {'arco': 'BC', 'rasparco': 'b', 'weight': 3})]
    print 'mstprim = ' +str(mstprim)                        
    for nds in G.nodes():
        posiz=L1.index(nds)+1              # posizione della label nella lista
        no=SOCKET_LIST[posiz]              # individuo socket riferito a quel nodo (label)
        no.send("riprist")
    for a in L2:
        pos=L2.index(a)
        ar=scka[pos]
        peso= G[nomearco[a][0]][nomearco[a][1]]['weight']  # diz= G['A']['B'], trovo value di key con [0]['weight']
        print 'peso: ' +str(peso)
        ar.send(str(peso))
    # forma le liste nodi e archi da seguire secondo algoritmo Prim 
    num=len(L1)-1
    i=0
    print 'i: ' +str(i)
    while i<num:
        if i==0:
            nodiMstPrim.append(mstprim[i][0])
            nodiMstPrim.append(mstprim[i][1])
            i=i+1
        else:
            if mstprim[i][0] in nodiMstPrim:
                nodiMstPrim.append(mstprim[i][1])
                i=i+1
            else:
                nodiMstPrim.append(mstprim[i][0])
                i=i+1
    p=0
    while p<num:
        archiMstPrim.append(mstprim[p][2]['rasparco'])
        p=p+1
    
# invia segnale di *tornare* alla modalità grafo costruito in partenza per poi lanciare una nuova modalita
def modalitaGrafo():
    global mod_albero
    mod_albero=0
    print ('Ritorno al grafo di partenza')
    print mod_albero
    del La1[:]
    del La2[:]
    del Lf1[:]
    del az[1:]              # lascio primo elemento che deve essere 'arco'
    del rasparco[:]
    del archiciclo[:]     
    del nodiattivati[:]   
    del daattivare[:]
    del nodiMstPrim[:]
    del archiMstPrim[:] 
    #del tempoarco[:]
    #del temponodo[:]
    A.clear()
    C.clear()
    for nds in G.nodes():
        posiz=L1.index(nds)         # posizione della label nella lista
        no=sck[posiz]               # individuo socket riferito a quel nodo (label)
        no.send("resetpl")
    for a in L2:
        pos=L2.index(a)
        ar=scka[pos]
        ar.send(str('resetpl'))
        

'''
=======================================================================
    FUNZIONE PRINCIPALE
=======================================================================
'''
def server():
    
    sessione = setupSession()                                           # recupero i dati log della sessione
    
    server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)   # si crea il socket
    server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1) # setto riutilizzo indirizzo
    server_socket.bind((HOST, PORT))                                    # bind sulla porta e host indicato
    server_socket.listen(20)                                            # num di connessioni accettabili

    # add server socket object to the list  of readable connections
    SOCKET_LIST.append(server_socket)
    
    print "In attesa dell'arrivo di nodi e archi dalla porta " + str(PORT)
    
    # funzione per scrivere log
    def scriviLog(logmessaggio):
        linealog= str(sessione) +', ' +(logmessaggio) +' | ' +str(datetime.datetime.now())
        storeLog(linealog)
    
    # funzione per invio messaggi ai client (nodes and edges)
    def invioMessaggio(tipo, posizione, messaggio):     # tipo= se sck o scka (socket raspnodo o rasparco)
        s=tipo[posizione]                               # posizione = socket riferito a quel rasp
        s.send(messaggio)                               # messaggio = cmd da inviare a quel rasp
    
    #===================================================================
    ''' PULSANTE CONFERMA: funzioni per il check grafo e albero '''
    #===================================================================
    
    controllo_grafo=True
     
    # funzione che accerta se il GRAFO nx.G costruito è connesso o no 
    def conferma(G):                                           
        if (nx.is_connected(G)):                    # verifica se G connesso
            scriviLog("Pulsante: creato un grafo semplice e connesso     ")
            for nodi in G.nodes():
                print nodi
                invioMessaggio(sck, L1.index(nodi), "grafook")
            for a in L2:
                invioMessaggio(scka, L2.index(a), "grafook")
            play_music(sigrafo, volume)
        else:                                       # nel caso non connesso
            scriviLog("Pulsante: ERRORE il grafo creato non è connesso   ")
            components=nx.connected_components(G)   # lista delle componenti non connesse
            lc=["purple", "giallo", "viola", "arancio", "azure", "brown"]
            i=0
            for c in components:
                print ("set")
                colore = lc[i]                      # stampa le label dei nodi A, B presenti nei diversi set (grafi non connessi)
                for el in c:
                    print el
                    invioMessaggio(sck, L1.index(el), str(colore))
                #i=i+1
                S=G.subgraph(c)
                print S.edges()                     # S.edges() = [('A', 'B')]
                for z in S.edges():
                    arcsub=z[0]+z[1]                # (AB)    
                    subarc=z[1]+z[0]                # (BA)
                    if arcsub in nomearco.values():
                        invioMessaggio(scka, L2.index(nomearco.keys()[nomearco.values().index(arcsub)]), str(colore))
                    elif subarc in nomearco.values():
                        invioMessaggio(scka, L2.index(nomearco.keys()[nomearco.values().index(subarc)]), str(colore))
                    else:
                        pass
                i=i+1
                # MANCA: inserire di inviare segnale agli archi che non fanno parte del subgraphs
            print ""
            play_music(nografo, volume)
    
    # funzione che ripristina il GRAFO nx.G come prima di premere il pulsante-conferma
    def ripristina(G):                              
        for node in G.nodes():
            invioMessaggio(sck, L1.index(node), "riprist")
        for a in nomearco.keys():
            invioMessaggio(scka, L2.index(a), "riprist")
    
    # funzione controllo se grafo costruito è quello fornito dall'insegnate
    def controlloGrafoIns():
        if set(G) == set(H) and set(G.edges()) == set(H.edges()):
            scriviLog("Pulsante: creato un grafo indicato da insegnante  ")
            for nodi in G.nodes():
                print nodi
                invioMessaggio(sck, L1.index(nodi), "grafook")
            for a in L2:
                invioMessaggio(scka, L2.index(a), "grafook")
            play_music(sigrafo, volume)
        else:
            scriviLog("Pulsante: ERRORE non creato il grafo indicato     ")
            for nodi in G.nodes():
                print nodi
                invioMessaggio(sck, L1.index(nodi), "error")
            for a in L2:
                invioMessaggio(scka, L2.index(a), "error")
            play_music(nografo, volume)
            
    # funzione per verificare se ALBERO nx.A costruito è ricoprente
    def albero(A):                                  # verificare se albero ricoprente
        if len(L1)==len(La1) and nx.is_connected(A):
            scriviLog("Pulsante: l'albero costruito è ricoprente  	")
            for nodi in A.nodes():
                invioMessaggio(sck, L1.index(nodi), "grafook")
            for a in La2:
                invioMessaggio(scka, L2.index(a), "grafook")
            play_music(sigrafo, volume)
        else:                                       # nel caso non  connesso
            nisol=[i for i in L1 if i not in La1]
            nconn=[i for i in L1 if i in La1]
            eisol=[i for i in L2 if i not in La2]
            econn=[i for i in L2 if i in La2]
            scriviLog("Pulsante: ERRORE l'albero non è ricoprente   ")
            lc=["viola", "arancio", "azure", "brown"]
            i=0
            for c in nisol:
                print "set"
                colore = lc[i]                      # stampa le label dei nodi A, B presenti nei diversi set (grafi non connessi)
                for el in c:
                    print el
                    invioMessaggio(sck, L1.index(el), str(colore))
                i=i+1
            for c in nconn:
                print 'set'
                for cn in c:
                    print cn
                    invioMessaggio(sck, L1.index(cn), str('giallo'))
            e=0
            for ei in eisol:
                print "set"
                colore = lc[e]                      # stampa le label dei nodi A, B presenti nei diversi set (grafi non connessi)
                for eli in ei:
                    print eli
                    invioMessaggio(scka, L2.index(eli), str(colore))
                e=e+1
            for ec in econn:
                print 'set'
                for cni in ec:
                    print cni
                    invioMessaggio(scka, L2.index(cni), str('giallo'))
            
            print ""
            play_music(nografo, volume)
    
    # funzione per ripristinare albero creato in precedenza
    def ripr_albero(A):
        scriviLog("Pulsante: ripristino l'albero creato in precedenza")
        isol=[i for i in L1 if i not in La1]        # nodi non presenti in albero
        conn=[i for i in L1 if i in La1]            # nodi presenti in albero
        eisol=[i for i in L2 if i not in La2]       # archi non presenti in arco
        for node in A.nodes():                      # individuo nodi presenti in albero
            invioMessaggio(sck, L1.index(node), "rialber")
        for nod in isol:                            # individuo nodi non presenti in albero
            invioMessaggio(sck, L1.index(nod), "riprist")
        for a in La2:                               # archi presenti in albero, quindi in La2
            print a
            invioMessaggio(scka, L2.index(a), "rialber")
        for ei in eisol:                            # archi presenti in L2 ma non in La2
            print ei
            invioMessaggio(scka, L2.index(ei), "riprist")
                
    # funzione per inviare ogni sei minuti messaggio ai nodi collegati al server
    def ci_sei():
        threading.Timer(360, ci_sei).start()
        for node in SOCKET_LIST[1:]:                # tutti i socket escluso il primo quello realtivo ala server
            invio=node.sendall('cisei')
            print invio
            #threading.Timer(60, ci_sei).start()
        
    ci_sei()
    
    #===================================================================
    # ciclo principale della funzione server
    #===================================================================
    while 1:
        time.sleep(0.05)
        # get the list sockets which are ready to be read through select
        # 4th arg, time_out  = 0 : poll and never block
        ready_to_read,ready_to_write,in_error = select.select(SOCKET_LIST,[],[],0)
            
        for sock in ready_to_read:
            # a new connection request recieved
            if sock == server_socket:
                sockfd, addr = server_socket.accept()       # accetto la comunicazione
                SOCKET_LIST.append(sockfd)              
                # output della SOCKET_LIST
                # [<socket._socketobject object at 0x7f3cb57f22f0>, <socket._socketobject object at 0x7f3cb57f2670>, ...]
            # a message from a client, not a new connection
            else:
                # process data recieved from client,
                try:
                    # receiving data from the socket.
                    data = sock.recv(RECV_BUFFER)+'-' +str(datetime.datetime.now()) +'| '         # provato ad inserire recvfrom cosi arriva dato e address       
                    print data
                    # arriva dato dal client, preleveo parte che mi interessa [:1]
                    cmd=data[0:7]       # messaggio inviato dal rasp-
                    idn=data[7:8]       # nome del rasp- ('A')
                    pin=data[8:10]      # numero pin (18, 16,  )
                    ora=data[-15:]      # orario arrivo data ('15:46:14.353806')
                    
                
                    #===================================================
                    ''' GRAFO: funzioni per raspnodo '''
                    #===================================================
                    
                    # Grafo: add in L4 parte arco connessa al nodo
                    def addEdgeNode():
                        if L4[0]==0:
                            L4[0]=data[7:10]
                            scriviLog("Grafo:  agganciato una parte di arco al nodo  " +str(data[7]) +'-' +str(data[8:10]))
                        else:
                            L4[1]=data[7:10]
                            scriviLog("Grafo:  agganciato una parte di arco al nodo  " +str(data[7]) +'-' +str(data[8:10]))
                        
                    
                    # Grafo: rimuove parte arco dal nodo
                    def removeEdgeNode():
                        global L4
                        if data[7:10] in L4:                                    # si rimuove solo una parte di arco appena inserito
                            scriviLog("Grafo:  rimosso una parte di arco dal nodo -> " + str(idn) +str('   '))
                            L4[L4.index(data[7:10])]=0                          # in L4 metto 0 al posto dell'elemento che ho disconesso                            
                        else:
                            ass = diz.keys()[diz.values().index([data[7:10]])]  # mi da la chiave associata al valore data[7:10] arrivato (che sarebbe il data[7:10] dell'altro nodo z.B:B21)
                            L4[0]=ass                                           # reinserisco in L4 *solo* l'altra parte di arco
                            del diz[data[7:10]]
                            del diz[ass]
                            
                    #===================================================
                    ''' GRAFO: funzioni per rasparco '''
                    #===================================================
                    
                    # Grafo: aggiunge edge al grafo e invia a rasp-arco cosa accendere
                    def addEdgeGraph():
                        ar=data[7]                      # prendo solo id del rasp-arco senza pin
                        global L4
                        if ar in L4:                    # se id-arco già in L4 allora add arco verificando se parallelo o selfloop
                            peso = random.randint(1,5)      # attribuisce al node un peso a random
                            p=str(L4[0][0])                 # p='A'
                            r=str(L4[1][0])                 # r='B'
                            par = (p, r)                    # ('A', 'B')
                            rap = (r, p)                    # ('B', 'A')
                            if par in G.edges():	        # se par è in G ==> formato arco parallelo
                                arco_parallelo()
                            elif rap in G.edges():		    # se rap è in G ==> formato arco parallelo
                                arco_parallelo()
                            else:
                                arc = L4[0][0]+L4[1][0]
                                G.add_edge(L4[0][0], L4[1][0], weight=peso, arco=arc, rasparco=data[7])   # add edge al grafo
                                lo=G.number_of_selfloops()
                                if lo == 1:			                    # se arco formato crea selfloop 
                                    arco_selfloop()
                                else:							        # altrimenti va a formare arco
                                    print '--> Add edge %s' % arc
                                    diz.setdefault(L4[0],[]).append(L4[1])      # add al diz key (nome edge), come value name node
                                    diz.setdefault(L4[1],[]).append(L4[0])      # e qui faccio il contrario di sopra
                                    scriviLog("Grafo:  arco'" +L4[2] +"' aggiunge 2-parte-arco al nodo " +str(L4[0][0]) +'-' +str(L4[0][1:3]))
                                    scriviLog("Grafo:  aggiunto al grafo l'arco -----------> " +str(L4[0][0]) +str(L4[1][0]) +str('  '))
                                    invioMessaggio(scka, L2.index(idn), 'edgeadd')
                                    nomearco[data[7]]=L4[0][0]+L4[1][0]         # add a {nomearco} il nuovo arco => {'a': 'BA'}
                                    L4=[0,0,0]                                  # reinserisco valori predefiniti
                        else:                       # arco non è ancora in L4 e quindi lo inserisce
                            L4[2]=ar
                            #scriviLog("Grafo:  arco'" +str(L4[2]) +" aggiunge 1a-parte-arco a nodo " +str(L4[0][0]) +'-' +str(L4[0][1:3]))
                    
                    # Grafo: creazione di un arco parallelo
                    def arco_parallelo():
                        global L4
                        scriviLog("Grafo:  ERRORE arco parallelo tra i nodi " + str(L4[1]) +' - ' +str(L4[0]))
                        invioMessaggio(scka, L2.index(idn), 'error')
                        diz.setdefault(L4[0],[]).append(L4[1]) 	        # add al diz --> 'key' (nome edge) + 'value' (name node)
                        diz.setdefault(L4[1],[]).append(L4[0])          # e qui faccio il contrario di sopra
                        G.add_edge(L4[0][0], L4[1][0])
                        for k, v in nomearco.iteritems():               # trovo il valore gia presente in {nomearco} e ...     
                            if v==L4[0][0]+L4[1][0]:                    
                                invioMessaggio(scka, L2.index(k), 'error')  # invio a quel rasp-arco il segnale
                            elif v==L4[1][0]+L4[0][0]:
                                invioMessaggio(scka, L2.index(k), 'error')
                        nomearco[data[7]]=L4[0][0]+L4[1][0]             # aggiungo a {nomearco} l'arco parallelo formato 
                        L4=[0,0,0]
                        
                    
                    # Grafo: creazione di un selfloop                
                    def arco_selfloop():
                        global L4
                        scriviLog("Grafo:  ERRORE creato un selfloop sul nodo    " +str(L4[0][0]+L4[1][0]) +"  ")
                        invioMessaggio(scka, L2.index(L4[2]), 'error') 
                        diz.setdefault(L4[0],[]).append(L4[1]) 	
                        diz.setdefault(L4[1],[]).append(L4[0])
                        nomearco[data[7]]=L4[0][0]+L4[1][0]             # add a {nomearco} nodo e pin = {'a': 'BA'}
                        L4=[0,0,0]
                        
                    # Grafo: rimuove arco dal grafo tramite rasp-arco
                    def removeEdgeGraph():
                        global L4
                        if data[7] in L4:               # si rimuove solo una parte di arco appena connessa
                            L4[2]=0
                            scriviLog("Grafo:  rimosso dal nodo la parte di arco --> " +str(data[7]) +str('   '))
                        else:
                            L4[2] = data[7]                             # reinserisco id-arco al 3posto in L4
                            G.remove_edge(nomearco[data[7]][0], nomearco[data[7]][1]) 
                            arcopar=nomearco[data[7]]                   # conservo la value ('AB') della key ('a') che sotto cancello 
                            pararco=arcopar[1]+arcopar[0]               # salvo il contrario ('BA'), serve dopo
                            del nomearco[data[7]]                       # elimino id-arco dal {nomearco} 
                            scriviLog("Grafo:  rimosso dal nodo la parte di arco --> " +str(data[7]) +str('   '))
                            invioMessaggio(scka, L2.index(data[7]), 'edgerem')
                            # se presente in {nomearco} una value ('AB') uguale a quella cancellata (arco parallelo) 
                            # invio a questo rasp-arco segnale di accendersi di bianco (si è rimosso l'arco parallelo)
                            # stessa cosa se presente una value contraria ('BA') 
                            if str(arcopar) in nomearco.values():
                                invioMessaggio(scka, L2.index(nomearco.keys()[nomearco.values().index(arcopar)]), 'edgeadd')
                            elif str(pararco) in nomearco.values():
                                invioMessaggio(scka, L2.index(nomearco.keys()[nomearco.values().index(pararco)]), 'edgeadd')
                            else:
                                pass
                            
                                     
                    #===================================================
                    ''' ALBERO: funzioni per raspnodo '''
                    #===================================================
                    
                    # Albero: aggiunta nodo secondo algoritmo Prim
                    def aggNodoPrim(idn):
                        La1.append(idn)
                        A.add_node(idn)
                        invioMessaggio(sck, L1.index(idn), 'aggnodo')
                        az.append('nodo')
                        scriviLog("Albero: aggiunto all'albero ricoprente il nodo " + str(idn) +"  ")
                        for idn, v in G.edges(idn):         # elenco archi che partono da questo nodo
                            Lf1.append(v)
                    
                    #Albero: verifica nodo adiacente secondo Prim
                    def verNodoFront():
                        f = idn in Lf1              # verifico se nodo scelto e' presente nella lista nodi frontiera 
                        if f == True:               # se presente add a La1 e add i suoi nodi frontiera a Lf1
                            aggNodoPrim(idn)
                        else:                       # se non presente in Lf1 segnalo l'errore
                            erroreNodoPrim()

                    # Albero: errore aggiunta nodo non adiacente secondo algoritmo Prim
                    def erroreNodoPrim():
                        scriviLog("Albero: ERRORE attivato un nodo non frontiera " + str(idn) +"  ")
                        invioMessaggio(sck, L1.index(idn), 'nonodo')
                        az.append('nodo')
                        A.add_node(idn)                                 # lo aggiungo cmq per poi toglierlo appena viene ripremuto pulsante
                        La1.append(idn)
                    
                    # da usare nel controllo ciclo quando arriva cmd da rasparco
                    def ciclo(grafo,logSi,logNo):
                        if len(list(nx.cycle_basis(grafo))) == 0:       # se non esiste ciclo nel grafo 
                            invioMessaggio(scka, L2.index(idn), 'arcoagg')      # invio messaggio al rasp-arco di accendersi
                            scriviLog(logSi)
                        else:                                           # altrimenti c'è un ciclo
                            for i in list(nx.find_cycle(grafo)):            # [('A', 'C'), ('C', 'B'), ('B', 'A')]
                                ab = [i][0][0]+[i][0][1]
                                ba = [i][0][1]+[i][0][0]
                                if ab in nomearco.values():
                                    rasp=nomearco.keys()[nomearco.values().index(ab)]   #recupero id-rasparco associato al value arco
                                    invioMessaggio(scka, L2.index(rasp), 'error')
                                    scriviLog(logNo)
                                    archiciclo.append(rasp)
                                elif ba in nomearco.values():
                                    rasp=nomearco.keys()[nomearco.values().index(ba)]
                                    invioMessaggio(scka, L2.index(rasp), 'error')
                                    scriviLog(logNo)
                                    archiciclo.append(rasp)
                
                    #===================================================
                    ''' ALBERO: funzioni per rasparco '''
                    #===================================================
                    
                    # Albero: rimuove arco dal nodo
                    def arco_albero_rimosso():
                        invioMessaggio(scka, L2.index(idn), 'rimarco')
                        A.remove_edge(La4[0][0],La4[1][0])
                        scriviLog("Albero: rimosso dai nodi " + str(La4[0]) + "e " + str(La4[1]))
                        del La4[0]               	                    # cancello primo elemento La4
                        del La4[0]

                    
                    #===================================================
                    ''' MST: funzioni per raspnodo '''
                    #===================================================
                   
                    # Albero: aggiunta nodo secondo algoritmo Prim al grafo M
                    def aggNodoMST(idn):
                        nodiattivati.append(idn)
                        az.append('nodo')
                        La1.append(idn)
                        A.add_node(idn)
                        invioMessaggio(sck, L1.index(idn), 'aggnodo')
                        scriviLog("MinSpT: aggiunto il nodo -------------------> " + str(idn) +"   ")

                    
                    '''
    #===================================================================
    #                MESSAGGI provenienti da RASPNODO e RASPARCO 
    #===================================================================
                    '''
                        
                    if data:
                        # there is something in the socket
                        sys.stdout.write(data)
                        
                        if cmd == 'iamlive':
                            print idn
                        
                        ### da decommentare se nodo si attiva con pulsante 
                        #if cmd == 'raspnod':                           # il rasp-nodosi aggancia al server
                            #sck.append(sockfd)                         # appendo alla lista sck il socket del nodo
                            #L1.append(idn)         
                        
                        if cmd == 'rasparc':                            # il rasp-nodosi aggancia al server
                            scka.append(sockfd)                         # appendo alla lista scka il socket dell'arco
                            L2.append(idn)
                            invioMessaggio(scka, L2.index(idn), 'connect')
                        '''  
            #===========================================================
            #            modalità GRAFO 
            #===========================================================
                        '''
                                       
                        if mod_albero==0:
                            
                            print 'Grafo: modalità costruzione grafo'
                            
                            if cmd=='finitoo': 
                                tempopuls.append(datetime.datetime.now())               # lo inserisco in quanto servirà per le px modalità
                                temponodo.append(datetime.datetime.now())
                                tem=(temponodo[-1]-temponodo[-2]).total_seconds()       # cfr time dell'ultimo e terzultimo inserito
                                if tem > 1:                                       
                                    if controllo_grafo:
                                        scriviLog("Grafo:  premuto il pulsante-conferma grafo        ")
                                        controllo_grafo=False
                                        if grafo_docente:
                                            controlloGrafoIns()
                                        else:
                                            conferma(G)
                                    else:
                                        scriviLog("Grafo:  ripremuto il pulsante-conferma            ")
                                        controllo_grafo=True
                                        ripristina(G)
                                else:
                                    pass
                            
                            elif cmd == 'addnode':                      # cmd che arriva dal nodo quando si usa il pulsante
                                L1.append(idn)      ### da togliere se nodo si attiva con il pulsante
                                sck.append(sockfd)  ### da togliere se nodo si attiva con il pulsante
                                G.add_node(idn)
                                scriviLog("Grafo:  aggiunto al grafo il nodo --------->  " + str(idn) +"   ")
                                indirizzo[idn]=addr                     # associo key e value nel diz 'indirizzo'
                                sockfd.send('Added a node to the graph')
                                
                            elif cmd=='rimnodo':
                                G.remove_node(idn)
                                sockfd.send("Removed node from the graph")
                                
                            elif cmd=='addedge':        # add edge con name node+edge dei primi "archi" che uniscono nodi
                                temponodo.append(datetime.datetime.now())
                                if len(temponodo)==1:                                   # primo arco ad essere aggiunto
                                    addEdgeNode()
                                else:
                                    tem=(temponodo[-1]-temponodo[-2]).total_seconds()   # diff tra ultimo e penultimo tempo arrivato
                                    if tem > 1:
                                        addEdgeNode()
                                    else:
                                        pass
                                    
                            elif cmd=='remedge':
                                temponodo.append(datetime.datetime.now())
                                if len(temponodo)==1:
                                    removeEdgeNode()
                                else:
                                    tem=(temponodo[-1]-temponodo[-2]).total_seconds()   # diff tra ultimo e penultimo tempo arrivato
                                    if tem > 1:
                                        removeEdgeNode()
                                    else:
                                        pass
                                    
                            elif cmd=='edgeadd':            # segnale in arrivo dall'arco
                                tempoarco.append(datetime.datetime.now())
                                if len(tempoarco)==1:
                                    addEdgeGraph()    
                                else:
                                    tem=(tempoarco[-1]-tempoarco[-2]).total_seconds()       # diff tra ultimo e penultimo tempo arrivato
                                    if tem > 1:
                                        addEdgeGraph()
                                    else:
                                        pass 
                                    
                            elif cmd=='edgerem':            # segnale in arrivo dall'arco
                                tempoarco.append(datetime.datetime.now())
                                tem=(tempoarco[-1]-tempoarco[-2]).total_seconds()       # diff tra ultimo e penultimo tempo arrivato
                                if tem > 1:
                                    removeEdgeGraph()
                                else:
                                    pass
                            else:
                                pass
                                #if sock in SOCKET_LIST:
                                #    SOCKET_LIST.remove(sock)
                            
                            '''
            #===========================================================
            #           ALBERO RICOPRENTE  
            #===========================================================
                            
                ======= modalità nodo-arco-nodo adiacenti =============='''
                        # si segue la sequenza nodo-arco-nodo adiacenti
                        # errore:   se si forma ciclo
                        #           se non si segue sequanza
                        
                        elif mod_albero==1:
                            
                            print 'Spanning Tree: modalità nodo-arco-nodo adiacenti'
                        
                            if cmd=='finitoo':
                                tempopuls.append(datetime.datetime.now())
                                tem=(tempopuls[-1]-tempopuls[-2]).total_seconds()       # cfr time dell'ultimo e terzultimo inserito
                                peso_albero=0
                                if tem > 1:
                                    if controllo_grafo:
                                        albero(A)
                                        scriviLog("STprim: Premuto pulsante-conferma - compito finito")
                                        controllo_grafo=False
                                    else:
                                        ripr_albero(A)
                                        scriviLog("STprim: Premuto pulsante-conferma ripristin albero")
                                        controllo_grafo=True
                                else:
                                    pass
                        
                            # AZIONE: attivo un nodo
                            # se primo nodo attivato:
                            #   add nodo a A.grafo + accendo nodo + aggiorno [az] + add nodo a [La1]
                            # se ultima [az] è arco + nodo in C.grafo (vuol dire aggiunto da ultimo arco attivato)
                            #   accendo nodo + add nodo a A.grafo + add arco a A.grafo + verifico se presente ciclo + aggiorno [az]
                            # altrimenti:
                            #   add nodo in C.grafo + invio errore + aggiorno [az]
                            # AZIONE: rimuovo nodo
                            # rimuovo nodo da A.grafo + rimuovo nodo da [La1] + spengo nodo + aggiorno [az]
                            #
                            # AZIONE: attivo arco
                            # se ultima [az] è 'nodo' e uno dei due nodi associati all'arco sono in [La1]:
                            #   add arco a C + aggiorno [az]
                            #   se non si forma un ciclo in C.grafo:
                            #       accendo arco
                            #   altrimenti:
                            #       invio errore
                            # altrimenti:
                            #       invio errore + aggiorno [az]
                            # AZIONE: rimuovo arco
                            # spengo arco + rimuovo arco da C.grafo + aggiorno [az] + tolgo nodo aggiunto da C.grafo
                                
                            elif cmd == 'aggnodo':
                                temponodo.append(datetime.datetime.now())
                                tem=(temponodo[-1]-temponodo[-2]).total_seconds()       # cfr time dell'ultimo e terzultimo inserito
                                if len(La1)==0:
                                    if tem> 1:             	# se primo posto La1 e' zero
                                        aggNodoPrim(idn)
                                    else:
                                        pass
                                else:
                                    if tem> 1:                     		# se La1 non e' vuota verifico se idn-nodoalb e' presente nella Lf1
                                        if az[-1]=='arco' and idn in C.nodes():		# se ultimo inserimento è un arco e nodo presente in grafo temp C
                                            aggNodoPrim(idn)
                                            aa=C.adj[idn].keys()                    # prendo nodo collegato al nodo idn
                                            A.add_edge(aa[0],idn)
                                            scriviLog("STprim: aggiunto all'albero ricoprente l'arco " +str(aa[0]) +str(idn) +"  ")
                                            # togliere commenti se si desidera che arco si accenda dopo che si è attivato nodo
                                            #if nomearco.has_key(idn+aa[0]):         # se presente in [nomearco]
                                                #invioMessaggio(scka, L2.index(nomearco[idn+aa[0]]), 'arcoagg')
                                            #elif nomearco.has_key(aa[0]+idn):       # se presente in [nomearco]
                                                #invioMessaggio(scka, L2.index(nomearco[aa[0]+idn]), 'arcoagg')                                                
                                            #else:
                                                #pass
                                            msgLog1="STprim: aggiunto all'albero l'arco ---------> " +str(aa[0]) +str(idn) +"  "
                                            msgLog2="STprim: ERRORE creato un ciclo con l'albero   " +str(aa[0]) +str(idn) +"  "
                                            if len(list(nx.cycle_basis(A))) == 0:       # se non esiste ciclo nel grafo 
                                                valu=aa[0]+idn            # AB
                                                luva=idn+aa[0]
                                                if valu in nomearco.values():
                                                    va=nomearco.keys()[nomearco.values().index(valu)]   # id-rasparco associato al nomearco AB
                                                    invioMessaggio(scka, L2.index(va), 'arcoagg')       # invio messaggio al rasp-arco di accendersi
                                                    scriviLog(msgLog1)
                                                elif luva in nomearco.values():
                                                    lu=nomearco.keys()[nomearco.values().index(luva)]   # id-rasparco associato al nomearco AB
                                                    invioMessaggio(scka, L2.index(lu), 'arcoagg')       # invio messaggio al rasp-arco di accendersi
                                                    scriviLog(msgLog1)
                                                else:
                                                    pass
                                            else:                                       # altrimenti c'è un ciclo
                                                for i in nx.find_cycle(A):
                                                    a=[i][0]
                                                    b=[i][1]
                                                    ab=G[a][b]['rasparco']
                                                    invioMessaggio(scka, L2.index(ab), 'error')
                                                    scriviLog(msgLog2)
                                        else:
                                            erroreNodoPrim()
                                    else:
                                        pass
                                        
                            elif cmd=='rimnodo':
                                temponodo.append(datetime.datetime.now())
                                tem=(temponodo[-1]-temponodo[-2]).total_seconds()       # cfr time dell'ultimo e terzultimo inserito
                                if tem > 1 :
                                    if len(az)==0:
                                        pass
                                    else:
                                        invioMessaggio(sck, L1.index(idn), 'rimnodo')
                                        del az[-1]
                                        A.remove_node(idn)
                                        del La1[La1.index(idn)]
                                        scriviLog("STprim: rimosso dall'albero ricoprente il nodo " +str(idn) +"  ")
                                else:
                                    pass
                                
                            elif cmd == 'arcoagg': 
                                tempoarco.append(datetime.datetime.now())
                                nodo0=nomearco[idn][0]          # id-nodo collegato all'arco
                                nodo1=nomearco[idn][1]          # altro id-nodo collegato allo stesso arco
                                La2.append(idn)
                                az.append('arco')
                                if az[-2] == 'nodo':                                    # condizione che ultima azione sia aggnodo 
                                    tem=(tempoarco[-1]-tempoarco[-2]).total_seconds()   # cfr time dell'ultimo e penultimo segnale arrivato da rasp-arco
                                    if tem > 1:
                                        if nodo0 in La1:                # se uno dei due nodi sono in La1 
                                            C.add_edge(nodo0, nodo1)
                                            msgLog1="STprim: attivato, ma non aggiunto, l'arco --> " +str(nodo0) +str(nodo1) +"  "
                                            msgLog2="STprim: ERRORE attivato un ciclo con l'albero " +str(nodo0) +str(nodo1) +"  "
                                            ciclo(C, msgLog1, msgLog2)                
                                        elif nodo1 in La1:              # se uno dei due nodi sono in La1 
                                            C.add_edge(nodo0, nodo1)
                                            msgLog1="STprim: attivato, ma non aggiunto, l'arco --> " +str(nodo0) +str(nodo1) +"  "
                                            msgLog2="STprim: ERRORE attivato un ciclo con l'albero " +str(nodo0) +str(nodo1) +"  "
                                            ciclo(C, msgLog1, msgLog2)
                                        else:                           # ERROR: si crea un arco tra dei nodi non attivi
                                            C.add_edge(nodo0, nodo1)
                                            invioMessaggio(scka, L2.index(idn), 'error')
                                            scriviLog("STprim: ERRORE attivato arco non uscente da nodo " +str(nodo0) +'   ')
                                    else:
                                        pass
                                        #del tempoarco[-1]                               # concello il datetime di questa operazione altrimenti aggarco dell'altro nodo non viene preso  
                                else:                                           # ERROR: ultima azione abbiamo inserito un arco
                                    tem=(tempoarco[-1]-tempoarco[-3]).total_seconds()       # cfr time dell'ultimo e terzultimo inserito
                                    if tem>1:
                                        invioMessaggio(scka, L2.index(idn), 'error')
                                        scriviLog("STprim: ERRORE attivato arco nodi non attivi " +str(nodo0+nodo1) +'  ')
                                    else:
                                        pass
                                        #del tempoarco[-1]
                            
                            elif cmd == 'arcorim':
                                tempoarco.append(datetime.datetime.now())
                                tem=(tempoarco[-1]-tempoarco[-2]).total_seconds()   # cfr time dell'ultimo e terzultimo inserito
                                if tem > 1:
                                    del az[-1:]
                                    C.remove_edge(nomearco[idn][0], nomearco[idn][1])
                                    invioMessaggio(scka, L2.index(idn), 'arcorim')
                                    scriviLog("STprim: rimosso dall'albero l'arco ---------> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                                    del La2[La2.index(idn)]             # rimuovo arco da La2
                                    if (nomearco[idn][0], nomearco[idn][1]) in A.edges():
                                        A.remove_edge(nomearco[idn][0], nomearco[idn][1])
                                        scriviLog("STprim: rimosso dall'albero l'arco ---------> " +str(nomearco[idn][0]) +str(nomearco[idn][1]) +"  ")
                                    elif (nomearco[idn][1], nomearco[idn][0]) in A.edges():
                                        A.remove_edge(nomearco[idn][1], nomearco[idn][0])
                                        scriviLog("STprim: rimosso dall'albero l'arco ---------> " +str(nomearco[idn][1]) +str(nomearco[idn][0]) +"   ")  
                                    # devo rimuovere anche inserimento fatto dal grafo del/i nodo/i in C
                                else:                                   # se il tem e' <1 allora non considerare stringa che arrivata
                                    pass
                            else:
                            # remove the socket that's broken
                                print 'cmd non trovato'
                                #if sock in SOCKET_LIST:
                                #    SOCKET_LIST.remove(sock)
                                
                            '''
            ============ modalita LIBERA ==============================='''
                            
                        # nodi e archi si attivano seguendo nessun ordine
                        # unica segnalazione di errore se viene creato un ciclo 
                            
                        elif mod_albero==2:
                            
                            print 'Spanning Tree: modalità libera'
                            
                            if cmd=='finitoo':
                                tempopuls.append(datetime.datetime.now())
                                temp=(tempopuls[-1]-tempopuls[-2]).total_seconds()              # cfr time dell'ultimo e terzultimo inserito
                                if temp > 1: 
                                    if controllo_grafo:
                                        albero(A)
                                        scriviLog("STfree: premuto pulsante-conferma - compito finito")
                                        controllo_grafo=False
                                    else:
                                        ripr_albero(A)
                                        scriviLog("STfree: premuto pulsante-conferma ripristin albero")
                                        controllo_grafo=True
                                else:
                                    pass
                        
                            # AZIONE: attivo un nodo
                            # inserisco nodo in A.grafo + aggiorno [La1] + accendo nodo
                            # se nodo presente in C.grafo (inserito da arco attivato in precedenza) 
                            #   e nodo a lui collegato da arco è in A.grafo:
                            #   inserisco arco in A.grafo 
                            #   verifico se si forma un ciclo
                            # altrimenti --> passo
                            # AZIONE: rimuovo un nodo
                            # aggiorno [La1] + rimuovo da A.grafo + invio segnale   
                            # AZIONE: attivo arco
                            # inserisco arco in C.grafo (e quindi anche i nodi che lo formano) + aggiorno La2
                            # se entrambi i nodi che formano l'arco sono in A.grafo: 
                            #   aggiungo arco a A.grafo 
                            #   verifico se si forma un ciclo in A.grafo
                            # altrimenti passo 
                            # AZIONE: rimuovo arco
                            # aggiorno [La2] + rimuovo arco da C.grafo
                            # se arco in A.grafo:
                            #   rimuovo arco da A.grafo
                            # altrimenti --> passo         
                        
                        
                            elif cmd == 'aggnodo':
                                temponodo.append(datetime.datetime.now())
                                temn=(temponodo[-1]-temponodo[-2]).total_seconds() 
                                if temn > 1:
                                    La1.append(idn)                 # inserisco in lista il nodo attivato
                                    invioMessaggio(sck, L1.index(idn), 'aggnodo')
                                    scriviLog("STfree: aggiunto all'albero ricoprente il nodo " +str(idn) +'  ')
                                    A.add_node(idn)
                                    if idn in C.nodes():            # se idn-raspnodo presente in C.nodes() 
                                        for i in C.adj[idn].keys():     # per ogni altro nodo collegato tramite arco a questo nodo (= ['C', 'B'])
                                            if i in A.nodes():              # se altro-nodo presente in A
                                                A.add_edge(idn,i)               # creo arco in A
                                                msgLog1="STfree: aggiunto all'albero l'arco ---------> " +str(idn) +str(i) +"  "
                                                msgLog2="STfree: ERRORE attivato un ciclo con l'albero " +str(idn) +str(i) +"  "
                                                if len(list(nx.cycle_basis(A))) == 0:       # se non esiste ciclo nel grafo 
                                                    valu=idn+i          # AB
                                                    luva=i+idn
                                                    if valu in nomearco.values():
                                                        va=nomearco.keys()[nomearco.values().index(valu)]   # id-rasparco associato al nomearco AB
                                                        invioMessaggio(scka, L2.index(va), 'arcoagg')       # invio messaggio al rasp-arco di accendersi
                                                        scriviLog(msgLog1)
                                                        if va in La2:
                                                            pass
                                                        else:
                                                            La2.append(va)
                                                    elif luva in nomearco.values():
                                                        lu=nomearco.keys()[nomearco.values().index(luva)]   # id-rasparco associato al nomearco AB
                                                        invioMessaggio(scka, L2.index(lu), 'arcoagg')       # invio messaggio al rasp-arco di accendersi
                                                        scriviLog(msgLog1)
                                                        if lu in La2:
                                                            pass
                                                        else:
                                                            La2.append(lu)
                                                    else:
                                                        pass
                                                else:                                       # altrimenti c'è un ciclo
                                                    for n in nx.find_cycle(A):
                                                        a=[n][0]
                                                        b=[n][1]
                                                        ab=G[a][b]['rasparco']
                                                        invioMessaggio(scka, L2.index(ab), 'error')
                                                        scriviLog(msgLog2)
                                            else:
                                                pass
                                    else:
                                        pass    
                                else:
                                    pass
                                            
                            elif cmd=='rimnodo':
                                temponodo.append(datetime.datetime.now())
                                temn=(temponodo[-1]-temponodo[-2]).total_seconds()
                                if temn > 1: 
                                    invioMessaggio(sck, L1.index(idn), 'rimnodo')
                                    if idn in La1:
                                        del La1[La1.index(idn)]
                                        A.remove_node(idn)
                                        scriviLog("STfree: rimosso dall'albero ricoprente il nodo " + str(idn) +'  ')
                                    else:
                                        pass
                                else:
                                    pass
                                    
                            elif cmd=='arcoagg':
                                if idn in La2:
                                    pass
                                else:
                                    La2.append(idn) 
                                invioMessaggio(scka, L2.index(idn), 'arcoagg')
                                C.add_edge(nomearco[idn][0], nomearco[idn][1])
                                scriviLog("STfree: aggiunto all'albero ricopr. C, l'arco " +str(idn) +"   ")
                                if nomearco[idn][0] and nomearco[idn][1] in A.nodes():                      # se i nodi collegati dall'arco sono in A.albero
                                    A.add_edge(nomearco[idn][0], nomearco[idn][1])
                                    nodo0=nomearco[idn][0]          # id-nodo collegato all'arco
                                    nodo1=nomearco[idn][1]          # altro id-nodo collegato allo stesso arco
                                    msgLog1="STfree: è stato aggiunto l'arco ------------> " +str(nodo0) +str(nodo1) +"  "
                                    msgLog2="STfree: ERRORE attivato un ciclo con l'albero " +str(nodo0) +str(nodo1) +"  "
                                    ciclo(A, msgLog1, msgLog2)     
                                else:
                                    pass
                                
                            elif cmd=='arcorim':
                                del La2[La2.index(idn)]
                                C.remove_edge(nomearco[idn][0], nomearco[idn][1])   
                                invioMessaggio(scka, L2.index(idn), 'arcorim')
                                scriviLog("STfree: rimosso l'arco 'temporaneo' --------> " +str(idn) +"   ")
                                if (nomearco[idn][0], nomearco[idn][1]) in A.edges():
                                    A.remove_edge(nomearco[idn][0], nomearco[idn][1])
                                    scriviLog("STfree: rimosso dall'albero l'arco ---------> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                                elif (nomearco[idn][1], nomearco[idn][0]) in A.edges():
                                    A.remove_edge(nomearco[idn][1], nomearco[idn][0])
                                    scriviLog("STfree: rimosso dall'albero l'arco ---------> " +str(nomearco[idn][1]+nomearco[idn][0]) +"  ")   
                                else:
                                    pass
                            else:
                                print 'cmd non trovato'
                                pass
                            '''
            #===========================================================                                
            #               modalità MST: minimum spanning tree 
            #===========================================================
                            
                ======= modalità libera ==============================='''
                        
                        # si possono inserire nodi e archi senza criterio
                        # al termine viene calcolato peso dell'albero creato
                        
                        elif mod_albero==3:
                            
                            print 'Minimum Spanning Tree: modalità libera'
                            
                            if cmd=='finitoo':
                                tempopuls.append(datetime.datetime.now())
                                temp=(tempopuls[-1]-tempopuls[-2]).total_seconds()              # cfr time dell'ultimo e terzultimo inserito
                                if temp > 1: 
                                    if controllo_grafo:
                                        albero(A)
                                        scriviLog("MSTfre: premuto pulsante-conferma - compito finito ")
                                        controllo_grafo=False
                                    else:
                                        ripr_albero(A)
                                        scriviLog("MSTfre: premuto pulsante-conferma ripristino albero")
                                        controllo_grafo=True
                                else:
                                    pass
                                                    
                            # AZIONE: inserisco un nodo 
                            # inserisco nodo in A.grafo + in [nodiattivati] + in[La1] --> serve per verifica albero ricprente 
                            # se questo nodo presente in C: (quindi forma arco in C)
                            #   e nodo a lui collegato da arco è in A
                            #   allora inserisco arco in albero A + verifico se presente ciclo
                            # altrimenti passo 
                            # AZIONE: rimuovo nodo
                            # tolgo nodo da A.grafo + tolgo da [nodiattivati]                
                            # AZIONE: inserisco un arco
                            # inserisco arco in grafo temporaneo C (e quindi anche i nodi che lo formano)
                            # se i nodi che formano l'arco sono in grafo A: 
                            #   add arco all'albero A. 
                            # altrimenti passo   
                            # AZIONE: rimuovo arco
                            # rimuovo arco da C.grafo + rimuovo arco se presente in A.grafo
                            # se [listaciclo] non vuota
                            #   invio arcoagg ai due archi che facevano parte del ciclo               
                                                    
                            elif cmd == 'aggnodo':
                                temponodo.append(datetime.datetime.now())
                                temn=(temponodo[-1]-temponodo[-2]).total_seconds()
                                if temn > 1: 
                                    invioMessaggio(sck, L1.index(idn), 'aggnodo')
                                    scriviLog("MSTfre: aggiunto all'albero ricoprente il nodo " +str(idn) +'  ')
                                    A.add_node(idn)
                                    La1.append(idn)
                                    # se nodo è in grafo.C e nodo a lui collegato è in grafo.A: add arco in grafo.A
                                    if idn in C.nodes():            # se idn-raspnodo presente in C.nodes() 
                                        for i in C.adj[idn].keys():     # per ogni altro nodo collegato tramite arco a questo nodo
                                            if i in A.nodes():              # se altro-nodo presente in A
                                                A.add_edge(idn, i, arco=G[idn][i]['arco'], peso=G[idn][i]['weight'], rasparco=G[idn][i]['rasparco'])               # creo arco in A 
                                                msgLog1="MSTfre: aggiunto all'albero l'arco ---------> " +str(idn) +str(i) +"  "
                                                msgLog2="MSTfre: ERRORE attivato un ciclo dall'albero  " +str(idn) +str(i) +"  "
                                                if len(list(nx.cycle_basis(A))) == 0:       # se non esiste ciclo nel grafo 
                                                    valu=idn+i          # AB
                                                    luva=i+idn          # BA
                                                    if valu in nomearco.values():
                                                        va=nomearco.keys()[nomearco.values().index(valu)]   # id-rasparco associato al nomearco AB
                                                        invioMessaggio(scka, L2.index(va), 'arcoagg')       # invio messaggio al rasp-arco di accendersi
                                                        scriviLog(msgLog1)
                                                        if va in La2:
                                                            pass
                                                        else:
                                                            La2.append(va)
                                                    elif luva in nomearco.values():
                                                        lu=nomearco.keys()[nomearco.values().index(luva)]   # id-rasparco associato al nomearco AB
                                                        invioMessaggio(scka, L2.index(lu), 'arcoagg')       # invio messaggio al rasp-arco di accendersi
                                                        scriviLog(msgLog1)
                                                        if lu in La2:
                                                            pass
                                                        else:
                                                            La2.append(lu)
                                                    else:
                                                        pass
                                            else:
                                                pass
                                    else:
                                        pass    
                                    
                                else: 
                                    pass
                                            
                            elif cmd=='rimnodo':
                                temponodo.append(datetime.datetime.now())
                                temn=(temponodo[-1]-temponodo[-2]).total_seconds() 
                                if temn > 1:
                                    invioMessaggio(sck, L1.index(idn), 'rimnodo')
                                    A.remove_node(idn)
                                    del La1[La1.index(idn)]
                                    scriviLog("MSTfre: rimosso dall'albero ricoprente il nodo " + str(idn) +'  ')
                                else:
                                    pass
                                    
                            elif cmd=='arcoagg':
                                if idn in La2:
                                    pass
                                else:
                                    La2.append(idn)
                                invioMessaggio(scka, L2.index(idn), 'arcoagg')
                                C.add_edge(nomearco[idn][0], nomearco[idn][1])
                                scriviLog("MSTfre: attivato, ma non aggiunto, l'arco --> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                                if nomearco[idn][0] and nomearco[idn][1] in A.nodes():
                                    aa=nomearco[idn][0]
                                    bb=nomearco[idn][1]
                                    A.add_edge(nomearco[idn][0], nomearco[idn][1], arco=G[aa][bb]['arco'], peso=G[aa][bb]['weight'], rasparco=G[aa][bb]['rasparco'])
                                    nodo0=nomearco[idn][0]              # id-nodo collegato all'arco
                                    nodo1=nomearco[idn][1]              # altro id-nodo collegato allo stesso arco
                                    msgLog1="MSTfre: è stato aggiunto l'arco ------------> " +str(nodo0+nodo1) +"  "
                                    msgLog2="MSTfre: ERRORE attivato un ciclo con l'albero " +str(nodo0+nodo1) +"  "
                                    ciclo(A, msgLog1, msgLog2)
                                else:
                                    pass
                            
                            elif cmd=='arcorim':
                                del La2[La2.index(idn)]
                                if len(archiciclo) is not 0:
                                    del archiciclo[archiciclo.index(idn)]
                                    for i in archiciclo:
                                        invioMessaggio(scka, L2.index(i), 'arcoagg')
                                        scriviLog("MSTfre: ciclo rimosso, reinserito l'arco ---> " +str(idn) +"   ")
                                C.remove_edge(nomearco[idn][0], nomearco[idn][1])   
                                invioMessaggio(scka, L2.index(idn), 'arcorim')
                                scriviLog("MSTfre: rimosso l'arco 'temporaneo' --------> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                                del archiciclo[:]
                                if (nomearco[idn][0], nomearco[idn][1]) in A.edges():
                                    A.remove_edge(nomearco[idn][0], nomearco[idn][1])
                                    scriviLog("MSTfre: rimosso dall'albero l'arco ---------> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                                elif (nomearco[idn][1], nomearco[idn][0]) in A.edges():
                                    A.remove_edge(nomearco[idn][1], nomearco[idn][0])
                                    scriviLog("MSTfre: rimosso dall'albero l'arco ---------> " +str(nomearco[idn][1]+nomearco[idn][0]) +"  ")   
                                else:
                                    pass
                                    
                            else:
                                print 'cmd non trovato'
                                pass
                            
                            '''
                ======= modalità: nodo-arco-nodo adiacenti ============='''
                        
                        elif mod_albero==4:
                            
                            print ' Minimum Spanning Tree: modalità nodo-arco-nodo adiacenti'
                            
                            if cmd=='finitoo':
                                tempopuls.append(datetime.datetime.now())
                                temp=(tempopuls[-1]-tempopuls[-2]).total_seconds()              # cfr time dell'ultimo e terzultimo inserito
                                if temp > 1: 
                                    if controllo_grafo:
                                        albero(A)
                                        scriviLog("MinSpT: premuto pulsante-conferma - compito finito  ")
                                        controllo_grafo=False
                                    else:
                                        ripr_albero(A)
                                        scriviLog("MinSpT: premuto pulsante-conferma ripristino albero")
                                        controllo_grafo=True
                                else:
                                    pass
                            
                            # AZIONE: attivo nodo 
                            # se in A.grafo non esiste nessun nodo:
                            #   lo aggiungo a A.grafo + aggiungo in [nodiattivati] + invio segnale ok + aggiorno [az]
                            # se nodo presente in A, in quanto inserito in seguito attivazione di un arco:
                            #   lo aggiungo  A.grafo + invio segnale ok + aggiorno [az] + add n [nodiattivati]
                            # altrimenti --> segnalo errore 
                            # AZIONE: rimuovo nodo
                            # aggiorno [az] + aggiorno [La1]
                            # se nodo in A.grafo:
                            #   lo tolgo da A.grafo + invio segnale 
                            # AZIONE: attivo arco  
                            # aggiorno [az]      
                            # se ultima [az] è nodo:
                            #   se arco è collegato ad un nodo di A.grafo:
                            #       aggiungo arco a A.grafo
                            #           se forma un ciclo: 
                            #               invio errore ad archi
                            #           altrimenti:
                            #               lo attivo + lo inserisco in A
                            # altrimenti --> segnalo errore (NON lo inserisco in A.grafo)
                            # AZIONE: rimuovo arco
                            # aggiorno [az]
                            # se arco presente in A.grafo:
                            #   aggiungo in A.grafo nodo presenti in [nodiattivati] (vengono rimossi quando tolgo arco da A.grafo)
                            
                            if cmd == 'aggnodo':
                                temponodo.append(datetime.datetime.now())
                                temn=(temponodo[-1]-temponodo[-2]).total_seconds() 
                                if temn > 1:
                                    if nx.number_of_nodes(A)==0:            # se primo nodo ad essere add al grafo M
                                        aggNodoMST(idn)
                                    else:
                                        if idn in A.nodes():		        # se nodo presente in A.grafo (vuol dire che stato add da arco in precedenza)
                                            aggNodoMST(idn)
                                        else:                               # altrimenti nodo non frontiera e non colleagot a ultimo arco attivato
                                            A.add_node(idn)
                                            La1.append(idn)
                                            az.append(idn)
                                            scriviLog("MinSpT: ERRORE nodo nell'attivare il nodo --> " + str(idn) +"  ")
                                            invioMessaggio(sck, L1.index(idn), 'nonodo')
                                else:
                                    pass
                            
                            elif cmd == 'rimnodo':
                                temponodo.append(datetime.datetime.now())
                                temn=(temponodo[-1]-temponodo[-2]).total_seconds() 
                                if temn > 1:
                                    del az[-1]
                                    if idn in A.nodes():
                                        A.remove_node(idn)
                                        del La1[La1.index(idn)]
                                        invioMessaggio(sck, L1.index(idn), 'rimnodo')
                                        scriviLog("MinSpT: rimosso il nodo --------------------> " + str(idn) +"   ")
                                    else:
                                        pass
                                else:
                                    pass
                            
                            elif cmd == 'arcoagg':
                                if az[-1]=='nodo':
                                    if nomearco[idn][0] in A.nodes():
                                        az.append('arco')
                                        peso=G.edge[nomearco[idn][0]][nomearco[idn][1]]['weight']        # peso dell'arco in G.grafo associato a A.grafo
                                        A.add_edge(nomearco[idn][0], nomearco[idn][1], weight=peso)
                                        giusto="MinSpT: attivato, ma non aggiunto, l'arco --> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  "
                                        sbagliato="MinSpT: ERRORE, attivato un ciclo con arco -> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  "
                                        ciclo(A, giusto, sbagliato) 
                                    elif nomearco[idn][1] in A.nodes():
                                        az.append('arco')
                                        peso=G.edge[nomearco[idn][0]][nomearco[idn][1]]['weight']
                                        A.add_edge(nomearco[idn][0], nomearco[idn][1], weight=peso)
                                        giusto="MinSpT: attivato, ma non aggiunto, l'arco --> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  "
                                        sbagliato="MinSpT: ERRORE, si è creato un ciclo con arco " +str(nomearco[idn][0]+nomearco[idn][1]) +"   "
                                        ciclo(A, giusto, sbagliato)                                      
                                    else:
                                        az.append('arco')
                                        invioMessaggio(scka, L2.index(idn), 'error')
                                        scriviLog("MinSpT: ERRORE, inserito l'arco ------------> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                                else:
                                    az.append('arco')
                                    invioMessaggio(scka, L2.index(idn), 'error')
                                    scriviLog("MinSpT: ERRORE, inserito l'arco ------------> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                                
                            elif cmd == 'arcorim':
                                del az[-1]
                                del archiciclo[:]
                                for x,y,z in A.edges(data='rasparco'):
                                    if z==idn:
                                        A.remove_edge(nomearco[idn][0], nomearco[idn][1])
                                if len(archiciclo) is not 0:
                                    del archiciclo[archiciclo.index(idn)]
                                    for i in archiciclo:
                                        invioMessaggio(scka, L2.index(i), 'arcoagg')
                                        scriviLog("MSTfre: ciclo rimosso, reinserito l'arco ---> " +str(idn) +"   ")
                                invioMessaggio(scka, L2.index(idn), 'arcorim')
                                scriviLog("MinSpT: rimosso l'arco ---------------------> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                                if nomearco[idn][0] in nodiattivati:
                                    A.add_node(nomearco[idn][0])
                                elif nomearco[idn][1] in nodiattivati:
                                    A.add_node(nomearco[idn][1])
                                else:
                                    pass
                                
                            '''
                ======= modalità secondo algoritmo PRIM ================'''            
                        
                        # creata lista del mst secondo prim
                        # si attivano nodo-arco-nodo segunedo l'ordine della lista
                        
                        elif mod_albero==5:
                            
                            print ' Minimum Spanning Tree: modalità algoritmo Prim'
                            
                            if cmd=='finitoo':
                                tempopuls.append(datetime.datetime.now())
                                temp=(tempopuls[-1]-tempopuls[-2]).total_seconds()              # cfr time dell'ultimo e terzultimo inserito
                                if temp > 1: 
                                    if controllo_grafo:
                                        albero(A)
                                        scriviLog("MSTprim: premuto pulsante-conferma, compito finito")
                                        controllo_grafo=False
                                    else:
                                        ripr_albero(A)
                                        scriviLog("MSTprim: premuto pulsante-conferma, riprist albero")
                                        controllo_grafo=True
                                else:
                                    pass
                            
                            # AZIONE: aggiungo nodo
                            # se non ci sono nodi in A.grafo e idn = a primo nodo di [nodiMstPrim]:
                            #   invio segnale + add a A.grafo + aggiorno [az]
                            # se [az] non vuota e ultimo elemento è arco
                            #   vedo lunghezza [nodiMstPrim]
                            #   se idn è uguale al nodo presente in [nodiMstPrim] nella posizione = a len+1 nodiA.grafo  
                            #   invio segnale + aggiorno [az]
                            # altrimenti:
                            #   invio errore + aggiorno [az] 
                            # AZIONE: rimuovo nodo
                            # tolgo ultimo elemento [az] + invio segnale 
                            # AZIONE: aggiungo arco
                            # controllo len A.grafo
                            # se idn = a quello posizionato in [archiMstPrim] + ultimo elemento [az] è nodo 
                            #   add arco a A.grafo + invio segnale
                            # altrimenti: 
                            #   invio errore + aggiorno [az]
                            # AZIONE: rimuovo arco
                            # invio segnale + aggiorno [az]  
                            
                            if cmd == 'aggnodo':
                                temponodo.append(datetime.datetime.now())
                                temn=(temponodo[-1]-temponodo[-2]).total_seconds() 
                                if temn > 1:
                                    posnod=len(La1) 
                                    if az[-1]=='arco' and idn==nodiMstPrim[posnod]:
                                        aggNodoMST(idn)
                                    else:
                                        erroreNodoPrim()
                                else:
                                    pass
                            
                            if cmd == 'rimnodo':
                                temponodo.append(datetime.datetime.now())
                                temn=(temponodo[-1]-temponodo[-2]).total_seconds() 
                                if temn > 1:
                                    del az[-1]
                                    A.remove_node(idn)
                                    del La1[La1.index(idn)]
                                    scriviLog("MinSpT: rimosso il nodo --------------------> " + str(idn) +"   ")
                                    invioMessaggio(sck, L1.index(idn), 'rimnodo')
                                else:
                                    pass
                            
                            if cmd == 'arcoagg':
                                posarc=len(A.nodes())-1
                                if az[-1]=='nodo':
                                    arp=archiMstPrim[posarc]
                                    az.append('arco')
                                    if idn==archiMstPrim[posarc]:
                                        A.add_edge(nomearco[idn][0], nomearco[idn][1])
                                        invioMessaggio(scka, L2.index(idn), 'arcoagg') 
                                        scriviLog("MinSpT: attivato l'arco --------------------> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                                    else:
                                        invioMessaggio(scka, L2.index(idn), 'error')
                                        scriviLog("MinSpT: ERRORE, inserito l'arco ------------> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                                else:
                                    az.append('arco')
                                    invioMessaggio(scka, L2.index(idn), 'error')
                                    scriviLog("MinSpT: ERRORE, inserire un nodo prima di arco" +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                            
                            
                            if cmd == 'arcorim':
                                del az[-1]
                                invioMessaggio(scka, L2.index(idn), 'arcorim')
                                scriviLog("MinSpT: rimosso dall'albero l'arco ---------> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                        
                
                            '''
                ======= modalità secondo algoritmo PRIM guidato ========'''            
                        
                        # creata lista del mst secondo prim
                        # si attivano nodo-arco-nodo segunedo l'ordine della lista
                        
                        elif mod_albero==6:
                            
                            print ' Minimum Spanning Tree: modalità algoritmo Prim guidato'
                            
                            if cmd=='finitoo':
                                tempopuls.append(datetime.datetime.now())
                                temp=(tempopuls[-1]-tempopuls[-2]).total_seconds()              # cfr time dell'ultimo e terzultimo inserito
                                if temp > 1: 
                                    if controllo_grafo:
                                        albero(A)
                                        scriviLog("MSTprim: premuto pulsante-conferma, compito finito")
                                        controllo_grafo=False
                                    else:
                                        ripr_albero(A)
                                        scriviLog("MSTprim: premuto pulsante-conferma, riprist albero")
                                        controllo_grafo=True
                                else:
                                    pass
                            
                            # AZIONE: aggiungo nodo
                            # se non ci sono nodi in A.grafo e idn = a primo nodo di [nodiMstPrim]:
                            #   invio segnale + add a A.grafo + aggiorno [az]
                            # se [az] non vuota e ultimo elemento è arco
                            #   vedo lunghezza [nodiMstPrim]
                            #   se idn è uguale al nodo presente in [nodiMstPrim] nella posizione = a len+1 nodiA.grafo  
                            #   invio segnale + aggiorno [az]
                            # altrimenti:
                            #   invio errore + blinko elemento giusto + aggiorno [az]
                            # AZIONE: rimuovo nodo
                            # tolgo ultimo elemento [az] + invio segnale 
                            # AZIONE: aggiungo arco
                            # controllo len A.grafo
                            # se idn = a quello posizionato in [archiMstPrim] + ultimo elemento [az] è nodo 
                            #   add arco a A.grafo + invio segnale
                            # altrimenti: 
                            #   invio errore + blinko elemento giusto + aggiorno [az] 
                            # AZIONE: rimuovo arco
                            # invio segnale + aggiorno [az]  
                            
                            if cmd == 'aggnodo':
                                temponodo.append(datetime.datetime.now())
                                temn=(temponodo[-1]-temponodo[-2]).total_seconds() 
                                if temn > 1:
                                    posnod=len(La1) 
                                    if az[-1]=='arco' and idn==nodiMstPrim[posnod]:
                                        aggNodoMST(idn)
                                    else:
                                        if az[-1]=='arco':
                                            invioMessaggio(sck, L1.index(L1[len(La1)]), 'guidato')
                                            erroreNodoPrim()
                                        else:
                                            invioMessaggio(scka, L2.index(L2[len(La2)]), 'guidato')
                                            erroreNodoPrim()
                                else:
                                    pass
                            
                            if cmd == 'rimnodo':
                                temponodo.append(datetime.datetime.now())
                                temn=(temponodo[-1]-temponodo[-2]).total_seconds() 
                                if temn > 1:
                                    del az[-1]
                                    A.remove_node(idn)
                                    del La1[La1.index(idn)]
                                    scriviLog("MinSpT: rimosso il nodo --------------------> " + str(idn) +"   ")
                                    invioMessaggio(sck, L1.index(idn), 'rimnodo')
                                else:
                                    pass
                            
                            if cmd == 'arcoagg':
                                posarc=len(La2)
                                if az[-1]=='nodo' and idn==archiMstPrim[posarc]:
                                    az.append('arco')
                                    La2.append(idn)
                                    A.add_edge(nomearco[idn][0], nomearco[idn][1])
                                    invioMessaggio(scka, L2.index(idn), 'arcoagg') 
                                    scriviLog("MinSpT: attivato l'arco --------------------> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                                else:
                                    invioMessaggio(scka, L2.index(idn), 'error')
                                    if az[-1]=='nodo':
                                        az.append('arco')
                                        scriviLog("MinSpT: ERRORE, non è giusto inserire l'arco  " +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                                        invioMessaggio(scka, L2.index(L2[len(La2)]), 'guidato')
                                    else:
                                        az.append('arco')
                                        scriviLog("MinSpT: ERRORE, inserire un nodo prima di arco" +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                                        invioMessaggio(sck, L1.index(L1[len(La1)]), 'guidato')
                                        
                            
                            if cmd == 'arcorim':
                                del az[-1]
                                invioMessaggio(scka, L2.index(idn), 'arcorim')
                                scriviLog("MinSpT: rimosso dall'albero l'arco ---------> " +str(nomearco[idn][0]+nomearco[idn][1]) +"  ")
                                    
                        else:
                            print 'cmd non trovato'
                        
                # exception
                except KeyboardInterrupt:
                    print 'Si chiude il server'
                    sys.exit()
                 #   broadcast(server_socket, sock, "Client (%s, %s) is offline\n" % addr)
                 #   continue
    
        
    server_socket.close()

def tastiera_server():
    print 'MODALITA:    st-free st-prim         grafo       mstfree     mstadiac    mstprim     mstguid'
    print 'ins=insertGraphIns   sock=listSocket sck=listSck scka=listScka           ind=diz_indirizzo '
    print 'Grafo NODO:  1=L1    4=L4            ng=nodi     eg=archi    g=grafo     tn=timeNodo'
    print 'Grafo ARCO:  2=L2    ar=nomearco     diz=arc-nod archi=parametri         ta=timeArco'
    print 'Albero NODO: 1a=La1  4a=La4          na=nodi-A   nc=nodi-C   Lf1=nodi_frontiera '
    print 'Albero ARCO: 2a=La2  az=listaAzioni  ea=archi-A  ec=archi-C  a=albero    ac=[archiciclo]'
    print 'MST:         natt=nodiAtt            npr=ndMst   apr=arMst   dat=[dattivare]    '     
    print 'MST calcoli peso:    pesomst=peso_mst            pesoalb=peso_A'  
    print 'k=cal_kruskal        p=calc_prim     kg=kruskal  pg=prim     step=prim passo-passo'
    print 'led=accende_5led     azzera=riparte da grafo     salvagra=salva grafo ' 
    #try:
    while 1:
            tasto=raw_input()
            if tasto == '1':
                print L1
            elif tasto == '2':
                print L2
            elif tasto == '4':
                print L4
            elif tasto == 'tn':
                print temponodo
            elif tasto == 'diz':
                print diz
            elif tasto == 'ar':
                print nomearco
            elif tasto == 'ta':
                print tempoarco
            elif tasto == 'lf1':
                print Lf1
            elif tasto == '1a':
                print La1
            elif tasto == '2a':
                print La2
            elif tasto == '4a':
                print La4
            elif tasto == 'n-gra':
                print G.number_of_nodes()
            elif tasto == 'e-gra':
                print G.number_of_edges()
            elif tasto == 'archi':    
                print '1: ' +str(G.edges(data=True))    # [('A', 'C', {'arco': 'CA', 'rasparco': 'c', 'weight': 2}), ('A', 'B', {'arco': 'AB', 'rasparco': 'f', 'weight': 5})]
                #print '5: ' +str(G['A']['B'])           # {0: {'arco': 'CA', 'rasparco': 'c', 'weight': 2}} ---  {0: {'arco': 'AB', 'rasparco': 'f', 'weight': 3}}
                #print '6: ' +str(G.adj['A'])            # {'C': {0: {'arco': 'CA', 'rasparco': 'c', 'weight': 2}}, 'B': {0: {'arco': 'AB', 'rasparco': 'f', 'weight': 5}}} --  {'C': {0: {'arco': 'CA', 'rasparco': 'c', 'weight': 2}}}
            elif tasto == 'archiH':    
                print '1: ' +str(H.edges(data=True))    # [('A', 'C', {'arco': 'CA', 'rasparco': 'c', 'weight': 2}), ('A', 'B', {'arco': 'AB', 'rasparco': 'f', 'weight': 5})]
                #print '5: ' +str(H['A']['B'])           # {0: {'arco': 'CA', 'rasparco': 'c', 'weight': 2}} ---  {0: {'arco': 'AB', 'rasparco': 'f', 'weight': 3}}
                #print '6: ' +str(H.adj['A'])            # {'C': {0: {'arco': 'CA', 'rasparco': 'c', 'weight': 2}}, 'B': {0: {'arco': 'AB', 'rasparco': 'f', 'weight': 5}}} --  {'C': {0: {'arco': 'CA', 'rasparco': 'c', 'weight': 2}}}
            elif tasto == 'ng':
                print G.nodes()
            elif tasto == 'eg':
                print G.edges()
            elif tasto == 'n-alb':
                print A.number_of_nodes()
            elif tasto == 'a-alb':
                print A.number_of_edges()
            elif tasto == 'na':
                print A.nodes()
            elif tasto == 'ea':
                print A.edges()
            elif tasto == 'nc':
                print C.nodes()
            elif tasto == 'ec':
                print C.edges()
            elif tasto == 'ac':
                print archiciclo
            elif tasto == 'natt':
                print nodiattivati
            elif tasto == 'dat':
                print daattivare    
            elif tasto == 'npr':
                print nodiMstPrim
            elif tasto == 'apr':
                print archiMstPrim
            elif tasto == 'ind':
                print indirizzo
            elif tasto == 'sock':
                print SOCKET_LIST
            elif tasto == 'sck':
                print sck
            elif tasto == 'ins':
                insertGrafoIns()
            elif tasto == 'scka':
                print scka
            elif tasto == 'az':
                print az
            elif tasto == 'st-prim':
                modalitaSTprim()
            elif tasto == 'st-free':
                modalitaSTlibera()
            elif tasto == 'grafo':
                modalitaGrafo()
            elif tasto == 'mstfree':
                modalitaMSTfree()
            elif tasto == 'mstadiac':
                modalitaMSTadiacenti()
            elif tasto == 'mstprim':
                modalitaMSTprim()
            elif tasto == 'mstguid':
                modalitaMSTguid()
            elif tasto == 'mst-list':
                print lista_mst   
            elif tasto == 'pesomst':
                print sommaPesiMst() 
            elif tasto == 'pesoalb':
                print sommaPesiAlb() 
            elif tasto == 'salvagra':
                salva_grafo(G.edges())
            elif tasto == 'ripristina':
                ripristina(G)
            elif tasto == 'k': 						#calcolo mst con Kruskal
                K=nx.minimum_spanning_tree(G)
                print(sorted(K.edges(data=True)))
            elif tasto == 'kg': 					#visualizzazione albero Kruskal
                pos = nx.spring_layout(K)
                nx.draw_networkx_nodes(K, pos, node_size=1500, node_color='#99ff00')
                nx.draw_networkx_edges(K, pos)
                nx.draw_networkx_edge_labels(K, pos)
                nx.draw_networkx_labels(K, pos)
                plot.axis('off')
                plot.show()
            elif tasto == 'p': 						# calcolo mst con Prim
                P=nx.prim_mst(G)
                print(sorted(P.edges(data=True)))
            elif tasto == 'pg': 					#visualizzazione albero Prim
                pos = nx.spring_layout(P)
                nx.draw_networkx_nodes(P, pos, node_size=1500, node_color='#99ffff')
                nx.draw_networkx_edges(P, pos)
                nx.draw_networkx_edge_labels(P, pos)
                nx.draw_networkx_labels(P, pos)
                plot.axis('off')
                plot.show()
            elif tasto == 'step': 					# visualizzazione passo passo algoritmo PRIM
                prim=prim_mst_edges(G, weight='weight', data=True)
                print(prim.next())
            elif tasto == 'g':
                # visualizzo grafo
                pos = nx.spring_layout(G)
                nx.draw_networkx_nodes(G, pos, node_size=1500, node_color='yellow')
                nx.draw_networkx_edges(G, pos, edge_color='r', widht=10)
                nx.draw_networkx_edge_labels(G, pos)
                nx.draw_networkx_labels(G, pos)
                plot.axis('off')
                plot.show()
            elif tasto == 'a':
                # visualizzo grafo
                pos = nx.spring_layout(A)
                nx.draw_networkx_nodes(A, pos, node_size=1500, node_color='yellow')
                nx.draw_networkx_edges(A, pos, edge_color='r', widht=10)
                nx.draw_networkx_edge_labels(A, pos)
                nx.draw_networkx_labels(A, pos)
                plot.axis('off')
                plot.show()
            elif tasto == 'led':      				# da schiacciare per testare i 5 led
                testLed()
            
                
    else:
           print 'fine ciclo '

    #except KeyboardInterrupt:
     #   print "Chiudo il server"


if __name__ == "__main__":

    try:

        # creo grafo vuoto
        G=nx.Graph()        # prima era G=nx.MultiGraph()
        A=nx.Graph()        # creazione albero
        C=nx.Graph()        # creazione albero temporaneo
        H=nx.Graph()        # creazione grafo realizzato dall'insegnante
        
        #T=nx.minimum_spanning_tree(G) # use Kruskal
        #mst=nx.minimum_spanning_edges(G,data=True)
        #edgelist=list(mst)
        #print(sorted(edgelist))

        t1 = Thread(target=server,args=())
        t2 = Thread(target=tastiera_server,args=())

        t1.start()
        t2.start()

    except KeyboardInterrupt:
        t1.__stop()
        t2.__stop()
        
        #sys.exit(server())
        #sys.exit(tastiera_server())
      
