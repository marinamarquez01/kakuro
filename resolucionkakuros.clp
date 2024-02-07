
;;; Resolución deductiva de un Kakuro
;;; Departamento de Ciencias de la Computación e Inteligencia Artificial 
;;; Universidad de Sevilla
;;;============================================================================

Marina Márquez Macías
DNI: 29503945M

;;;============================================================================
;;; Representación del Kakuro
;;;============================================================================

;;;   Utilizaremos la siguiente plantilla para representar las celdas del
;;; Kakuro. Cada celda tiene los siguientes campos:
;;; - id: Identificador único de la celda
;;; - fila: Número de fila en la que se encuentra la celda
;;; - columna: Número de columna en la que se encuentra la celda
;;; - rango: Rango de valores que se pueden colocar en la celda. Inicialmente
;;;   el rango son todos los valores numéricos de 1 a 9.

(deftemplate celda
  (slot id)
  (slot fila)
  (slot columna)
  (multislot rango
             (default (create$ 1 2 3 4 5 6 7 8 9))))

;;;   De esta forma, una celda tendrá un valor asignado si y solo si dicho
;;; valor es el único elemento del rango.

;;;   La siguiente variable global sirve enumerar las restricciones del puzle.

(defglobal ?*restricciones* = 0)

;;;   La siguiente función sirve para asignar de forma automática y única
;;; identificadores a las restricciones del puzle. 

(deffunction idRestriccion ()
  (bind ?*restricciones* (+ ?*restricciones* 1))
  ?*restricciones*)

;;;   Utilizaremos la siguiente plantilla para almacenar las restricciones del
;;; puzle. Cada restricción tiene los siguientes campos:
;;; - id: Identificador único de la restricción
;;; - valor: Valor de la restricción
;;; - casillas: Identificadores de las casillas que se ven afectadas por la
;;;   restricción

(deftemplate restriccion
  (slot id
        (default-dynamic (idRestriccion)))
  (slot valor)
  (multislot casillas))

;;;============================================================================
;;; Estrategias de resolución
;;;============================================================================

;;;   El objetivo del ejercicio consiste en implementar un conjunto de reglas
;;; CLIPS que resuelvan un Kakuro de forma deductiva, es decir, deduciendo el
;;; valor de una casilla a partir de reglas que analicen los posibles valores
;;; de las casillas relacionadas.




;;;============================================================================
;;; Reglas para imprimir el resultado
;;;============================================================================

;;;   Las siguientes reglas permiten visualizar el estado del puzle, una vez
;;; aplicadas todas las reglas que implementan las estrategias de resolución.
;;; La prioridad de estas reglas es -10 para que sean las últimas en
;;; aplicarse.

;;;   Para las casillas del tablero con un único valor en su rango se indica
;;; dicho valor, para las casillas del tablero en las que no se haya podido
;;; deducir el valor se indica el símbolo '?'. El resto de las casillas hasta
;;; completar la cuadrícula 9x9 se dejan en blanco.

(defrule imprime-solucion
  (declare (salience -10))
  =>
  (printout t "+---------+" crlf "|")
  (assert (imprime 1 1)))

(defrule imprime-celda-1
  (declare (salience -10))
  ?h <- (imprime ?i ?j&:(<= (* ?i ?j) 81))
  (celda (fila ?i) (columna ?j) (rango $?v))
  =>
  (retract ?h)
  (if (= (length$ $?v) 1)
      then (printout t (nth$ 1 $?v))
    else (printout t "?"))
  (if (= ?j 9)
      then (printout t "|" crlf))
  (if (and (= ?i 9) (= ?j 9))
      then (printout t "+---------+" crlf))
  (if (and (= ?j 9) (not (= ?i 9)))
      then (printout t "|")
           (assert (imprime (+ ?i 1) 1))
    else (assert (imprime ?i (+ ?j 1)))))

(defrule imprime-celda-2
  (declare (salience -10))
  ?h <- (imprime ?i ?j&:(<= (* ?i ?j) 81))
  (not (celda (fila ?i) (columna ?j) (rango $?v)))
  =>
  (retract ?h)
  (printout t " ")
  (if (= ?j 9)
      then (printout t "|" crlf))
  (if (and (= ?i 9) (= ?j 9))
      then (printout t "+---------+" crlf))
  (if (and (= ?j 9) (not (= ?i 9)))
      then (printout t "|")
           (assert (imprime (+ ?i 1) 1))
    else (assert (imprime ?i (+ ?j 1)))))

;;;============================================================================
;;; Funcionalidad para leer los puzles del fichero de ejemplos
;;;============================================================================

;;;   Esta función crea una lista de identificadores de casillas en horizontal.

(deffunction crea-casillas-horizontal (?f ?c ?n)
  (bind ?datos (create$))
  (loop-for-count
   (?i 0 (- ?n 1))
   (bind ?datos (insert$ ?datos ?n (eval (str-cat ?f (+ ?c ?i))))))
  ?datos)

;;;   Esta función construye los hechos que representan las restricciones de
;;; una línea horizontal del Kakuro.

(deffunction procesa-restricciones-fila (?f $?linea)
  (bind ?i 1)
  (bind ?d (nth$ ?i $?linea))
  (while (< ?i 9)
    (bind ?v 0)
    (while (and (<= ?i 9) (not (numberp ?d)))
      (bind ?i (+ ?i 1))
      (bind ?d (nth$ ?i $?linea)))
    (bind ?c ?i)
    (while (and (<= ?i 9) (numberp ?d))
      (bind ?i (+ ?i 1))
      (bind ?v (+ ?v ?d))
      (bind ?d (nth$ ?i $?linea)))
    (if (< 0 (- ?i ?c))
        then (assert (restriccion
                      (valor ?v)
                      (casillas
                       (crea-casillas-horizontal ?f ?c (- ?i ?c)))))))
  TRUE)

;;;   Esta función crea una lista de identificadores de casillas en vertical.

(deffunction crea-casillas-vertical (?f ?c ?n)
  (bind ?datos (create$))
  (loop-for-count
   (?i 0 (- ?n 1))
   (bind ?datos (insert$ ?datos ?n (eval (str-cat (+ ?f ?i) ?c)))))
  ?datos)

;;;   Esta función construye los hechos que representan las restricciones de
;;; una línea horizontal del Kakuro.

(deffunction procesa-restricciones-columna (?c $?linea)
  (bind ?i 1)
  (bind ?d (nth$ ?i $?linea))
  (while (< ?i 9)
    (bind ?v 0)
    (while (and (<= ?i 9) (not (numberp ?d)))
      (bind ?i (+ ?i 1))
      (bind ?d (nth$ ?i $?linea)))
    (bind ?f ?i)
    (while (and (<= ?i 9) (numberp ?d))
      (bind ?i (+ ?i 1))
      (bind ?v (+ ?v ?d))
      (bind ?d (nth$ ?i $?linea)))
    (if (< 0 (- ?i ?f))
        then (assert (restriccion
                      (valor ?v)
                      (casillas
                       (crea-casillas-vertical ?f ?c (- ?i ?f)))))))
  TRUE)

;;;   Esta función construye todos los hechos que representan las restricciones
;;; de un Kakuro dado en el formato utilizado en el fichero de ejemplos.

(deffunction procesa-restricciones-ejemplo (?datos)
  (loop-for-count
   (?i 1 9)
   (bind $?linea (create$))
   (loop-for-count
    (?j 2 10)
    (bind ?linea (insert$ ?linea 10
                          (eval (sub-string (+ (* 10 ?i) ?j)
                                            (+ (* 10 ?i) ?j) ?datos)))))
   (procesa-restricciones-fila ?i ?linea))
  (loop-for-count
   (?j 2 10)
   (bind $?linea (create$))
   (loop-for-count
    (?i 1 9)
    (bind ?linea (insert$ ?linea 10
                          (eval (sub-string (+ (* 10 ?i) ?j)
                                            (+ (* 10 ?i) ?j) ?datos)))))
   (procesa-restricciones-columna (- ?j 1) ?linea))
  TRUE)

;;;   Esta función localiza el Kakuro que se quiere resolver en el fichero de
;;; ejemplos.

(deffunction lee-kakuro (?n)
  (open "ejemplos.txt" data "r")
  (loop-for-count (?i 1 (- ?n 1))
                  (readline data))
  (bind ?datos (readline data))
  (procesa-restricciones-ejemplo ?datos)
  (close data))

;;;   Esta regla pregunta al usuario que número de Kakuro del fichero de
;;; ejemplos se quiere resolver y genera los hechos que representan las
;;; restricciones asociadas.

(defrule kakuro-numero
  (declare (salience 100))
  =>
  (printout t "Qué problema quieres resolver (1-50)? : ")
  (lee-kakuro (read)))

;;;   Esta regla construye las celdas que aparecen en alguna de las
;;; restricciones del Kakuro que se quiere resolver.

(defrule crea-celdas-restricciones
  (declare (salience 100))
  (restriccion (casillas $? ?id $?))
  (not (celda (id ?id)))
  =>
  (assert (celda (id ?id) (fila (div ?id 10)) (columna (mod ?id 10)))))

;;;============================================================================




;;;============================================================================
;;; Reglas generales
;;;============================================================================

;;; Si hay una restricción aplicada a una única casilla o celda, y su valor es menor o igual que 9,
;;; solucionar celda asignando el valor de la restriccion.

(defrule restriccion-con-una-casilla
  (declare (salience 90))
  ?h1 <- (restriccion (valor ?v&:(<= ?v 9)) (casillas ?c))
  ?h2 <- (celda (id ?i&:(eq ?i ?c)) (rango $?))     
  =>
  (modify ?h2 (rango ?v)))



;;; Si hay un grupo de casillas con una restriccion <= 9, dejar en el rango de valores
;;; de la celda el rango de valores desde 1 hasta el valor de la restriccion 
;;; menos 1. Como por defecto el rango tiene los valores del 1 al 9 ordenadis, si la restriccion es por
;;; ejemplo 7, se debe dejar en el rango los valores del 1 al 6, ya que al menos hay dos casillas 
;;; que cumplen con la restricción (pues si no, se aplicaría la regla anterior y no esta), y el valor
;;; más pequeño que podria tomar una de ellas sería 1, por lo tanto la otra tomaría el valor 6.

(defrule eliminar-valores-mayores-restriccion
  (declare (salience 90))
  ?h1 <- (restriccion (valor ?v&:(<= ?v 9)) (casillas $? ?c $?))
  ?h2 <- (celda (id ?i&:(eq ?i ?c)) (rango $?u ?r&:(eq ?r ?v) $?w))    
  =>
  (modify ?h2 (rango $?u)))
  
  

;;; Si en un grupo de celdas para una restriccion ya hay una resuelta, eliminar 
;;; el valor de esa celda del rango del resto de celdas a las que se aplica dicha restriccion, 
;;; por filas.

(defrule eliminar-valores-asignados-fila
  ?h1 <- (restriccion (valor ?v) (casillas $?j1 ?j $?j2))
  ?h2 <- (celda (id ?i&:(eq ?i ?j)) (fila ?f1) (columna ?c1) (rango $?u ?r1&:(<= ?r1 ?v) $?w))
  ?h3 <- (celda (id ?k&~?i) (fila ?f2&:(eq ?f2 ?f1)) (columna ?c2&~?c1) (rango $?u1 ?r2&:(eq ?r2 ?r1) $?w1))
  (test (and (eq (length$ $?u) 0) (eq (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0) (> (length$ $?w1) 0)))
  (test (or (member$ ?k $?j1) (member$ ?k $?j2)))
  =>
  (modify ?h3 (rango $?u1 $?w1)))
  
  

;;; Si en un grupo de celdas para una restriccion ya hay una resuelta, eliminar 
;;; el valor de esa celda del rango del resto de celdas a las que se aplica dicha restriccion, 
;;; por columnas.

(defrule eliminar-valores-asignados-columna
  ?h1 <- (restriccion (valor ?v) (casillas $?j1 ?j $?j2))
  ?h2 <- (celda (id ?i&:(eq ?i ?j)) (fila ?f1) (columna ?c1) (rango $?u ?r1&:(<= ?r1 ?v) $?w))  
  ?h3 <- (celda (id ?k&~?i) (fila ?f2&~?f1) (columna ?c2&:(eq ?c2 ?c1)) (rango $?u1 ?r2&:(eq ?r2 ?r1) $?w1))
  (test (and (eq (length$ $?u) 0) (eq (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0) (> (length$ $?w1) 0)))
  (test (or (member$ ?k $?j1) (member$ ?k $?j2)))
  =>
  (modify ?h3 (rango $?u1 $?w1)))




;;;============================================================================
;;; Reglas que resuelven restricciones que aplican a exactamente 2 celdas
;;;============================================================================



;;; Si hay una restriccion par con un valor <= 18 aplicada a dos casillas, en sus casillas no puede estar 
;;; el valor medio de la restricción, puesto que si no, se repetiría el valor en la otra casilla. 
;;; Por ejemplo, restriccion 18 aplicada a dos casillas no se puede resolver con 9 en ninguna
;;; de las casillas.

(defrule eliminar-valor-entre-2-si-par-menor-igual-18
  (declare (salience 80))
  ?h1 <- (restriccion (valor ?v&:(and (eq (mod ?v 2) 0) (<= ?v 18))) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(or (eq ?i ?c1) (eq ?i ?c2))) (rango $?u ?r&:(eq ?r (div ?v 2)) $?w))
  =>
  (modify ?h2 (rango $?u $?w)))
  
  
  
;;; Si una restricción de fila se aplica a dos celdas, y una de ellas está resuelta, 
;;; entonces el valor asignado a la otra celda será la resta del valor de la restriccion
;;; menos el valor de la celda resuelta.

(defrule 2-fila-1res
  ?h1 <- (restriccion (valor ?v&:(<= ?v 9)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(or (eq ?i ?c1) (eq ?i ?c2))) (fila ?f1) (columna ?col1) (rango ?r1&:(<= ?r1 ?v)))    ;
  ?h3 <- (celda (id ?j&:(or (eq ?j ?c1) (eq ?j ?c2))) (fila ?f1) (columna ?col2&~?col1) (rango $?u ?r2&:(<= ?r2 ?v) $?w))
  (test (neq ?i ?j))
  (test (or (> (length$ $?u) 0) (> (length$ $?w) 0)))
  (test (neq ?r1 ?r2))
  (test (eq (- ?v ?r1) ?r2))
  =>
  (modify ?h3 (rango ?r2)))
  
  
  
;;; Si una restricción de columna se aplica a dos celdas, y una de ellas está resuelta, 
;;; entonces el valor asignado a la otra celda será la resta del valor de la restriccion
;;; menos el valor de la celda resuelta.

(defrule 2-col-1res
  ?h1 <- (restriccion (valor ?v&:(<= ?v 9)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(or (eq ?i ?c1) (eq ?i ?c2))) (fila ?f1) (columna ?col2) (rango ?r1&:(<= ?r1 ?v)))
  ?h3 <- (celda (id ?j&:(or (eq ?j ?c1) (eq ?j ?c2))) (fila ?f2&~?f1) (columna ?col2) (rango $?u ?r2&:(<= ?r2 ?v) $?w))
  (test (neq ?i ?j))
  (test (or (> (length$ $?u) 0) (> (length$ $?w) 0)))
  (test (neq ?r1 ?r2))
  (test (eq (- ?v ?r1) ?r2))
  =>
  (modify ?h3 (rango ?r2)))
  

;;; Creo que estas dos son iguales
(defrule resolver-conjunto-2cas-fila-mayor-9
  ?h1 <- (restriccion (valor ?v&:(> ?v 9)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(or (eq ?i ?c1) (eq ?i ?c2))) (fila ?fh2) (columna ?ch2) (rango $?inih2 ?r1&:(<= ?r1 ?v) $?finh2))
  ?h3 <- (celda (id ?j&:(or (eq ?j ?c1) (eq ?j ?c2))) (fila ?fh3&:(eq ?fh3 ?fh2)) (columna ?ch3&:(neq ?ch3 ?ch2)) (rango $?inih3 ?r2&:(<= ?r2 ?v) $?finh3))
  (test (neq ?i ?j))
  (test (and (eq (length$ $?inih2) 0) (eq (length$ $?finh2) 0)))
  (test (or (> (length$ $?inih3) 0) (> (length$ $?finh3) 0)))
  (test (neq ?r1 ?r2))
  (test (eq (+ ?r1 ?r2) ?v))
  =>
  (modify ?h3
        (rango ?r2)))

(defrule resolver-conjunto-2cas-columna-mayor-9
  ?h1 <- (restriccion (valor ?v&:(> ?v 9)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i&:(or (eq ?i ?c1) (eq ?i ?c2))) (fila ?fh2) (columna ?ch2) (rango $?inih2 ?r1&:(<= ?r1 ?v) $?finh2))
  ?h3 <- (celda (id ?j&:(or (eq ?j ?c1) (eq ?j ?c2))) (fila ?fh3&:(neq ?fh3 ?fh2)) (columna ?ch3&:(eq ?ch3 ?ch2)) (rango $?inih3 ?r2&:(<= ?r2 ?v) $?finh3))
  (test (neq ?i ?j))
  (test (and (eq (length$ $?inih2) 0) (eq (length$ $?finh2) 0)))
  (test (or (> (length$ $?inih3) 0) (> (length$ $?finh3) 0)))
  (test (neq ?r1 ?r2))
  (test (eq (+ ?r1 ?r2) ?v))
  =>
  (modify ?h3
        (rango ?r2)))

;;;============================================================================

;;; Una restriccion cuyo valor es <= 18 y que aplique a exactamente 2 celdas, probar todas las combinaciones
;;; y dejar solo aquellas cuyo resultado de sumar dos valores sea exactmente el valor de la restriccion

(defrule probar-candidatos-dos-celdas
  (declare (salience -5))
  ?h1 <- (restriccion (valor ?v&:(<= ?v 18)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?i1&:(or (eq ?i1 ?c1) (eq ?i1 ?c2))) (rango $?r1))
  ?h3 <- (celda (id ?i2&:(or (eq ?i2 ?c1) (eq ?i2 ?c2))) (rango $?r2))
  (test (neq ?i1 ?i2))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r2) 1))
  =>
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r1))
    (bind ?a (nth$ ?i $?r1))
    (while (<= ?j (length$ $?r2))
      (bind ?b (nth$ ?j $?r2))
      (if (eq ?v (+ ?a ?b))
        then (printout t "Result: " (+ ?a ?b) " , value: " ?v crlf)
             (bind ?cont (+ ?cont +1)) ;
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidato1))
         (modify ?h3 (rango ?candidato2))))
         
         
         
         
;;;============================================================================
;;; Reglas que resuelven restricciones que aplican a exactamente 3 celdas
;;;============================================================================

;;; Si una restriccion aplica sobre 3 casillas, y dos de ellas estan resueltas
;;; aplicar a la resultante la resta del valor de la restriccion con los dos valores asignados

; Falta por resolver la primera casilla:

(defrule 3-casillas-2-resueltas1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  (test (> (length$ $?r1) 1))
  =>
  (bind ?sol (- ?v (+ ?r2 ?r3)))
  (if (<= ?sol 9)
    then (modify ?h2 (rango ?sol))))
    
    
   
; Falta por resolver la segunda casilla:

(defrule 3-casillas-2-resueltas2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  (test (> (length$ $?r2) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 ?r3)))
  (if (<= ?sol 9)
    then (modify ?h3 (rango ?sol))))
    
    

; Falta por resolver la segunda casilla:

(defrule 3-casillas-2-resueltas3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  (test (> (length$ $?r3) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 ?r2)))
  (if (<= ?sol 9)
    then (modify ?h4 (rango ?sol))))


;;;============================================================================

;;; Si una restriccion se aplica sobre 3 casillas, y una de ellas esta resuelta
;;; probar combinaciones y asignar si solo hay una posible.



; La casilla resuelta es la primera:

(defrule 3-casillas-1-resuelta1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  (test (> (length$ $?r2) 1))
  (test (> (length$ $?r3) 1))
  =>
  (bind ?v (- ?v ?r1))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r2))
    (bind ?a (nth$ ?i $?r2))
    (while (<= ?j (length$ $?r3))
      (bind ?b (nth$ ?j $?r3))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h3 (rango ?candidato1))
         (modify ?h4 (rango ?candidato2))))
         
         
         
; La casilla resuelta es la segunda:

(defrule 3-casillas-1-resuelta2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r3) 1))
  =>
  (bind ?v (- ?v ?r2))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r1))
    (bind ?a (nth$ ?i $?r1))
    (while (<= ?j (length$ $?r3))
      (bind ?b (nth$ ?j $?r3))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidato1))
         (modify ?h4 (rango ?candidato2))))



; La casilla resuelta es la tercera:

(defrule 3-casillas-1-resuelta3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r2) 1))
  =>
  (bind ?v (- ?v ?r3))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r1))
    (bind ?a (nth$ ?i $?r1))
    (while (<= ?j (length$ $?r2))
      (bind ?b (nth$ ?j $?r2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidato1))
         (modify ?h3 (rango ?candidato2))))



;;;============================================================================

;;; Si una restriccion aplica sobre 3 casillas y no hay ninguna resuelta, probar 
;;; combinaciones y asingar si solo hay una posible.


(defrule 3-casillas-0-resueltas
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r2) 1))
  (test (> (length$ $?r3) 1))
  =>
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?candidato3 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?k 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r1))
    (bind ?a (nth$ ?i $?r1))
    (while (<= ?j (length$ $?r2))
      (bind ?b (nth$ ?j $?r2))
      	(while (<= ?k (length$ $?r3))
      		(bind ?c (nth$ ?k $?r3))
      			(if (and (eq ?v (+ ?a (+ ?b ?c))) (neq ?a ?b) (neq ?a ?c) (neq ?b ?c))
        			then
             		(bind ?cont (+ ?cont +1)) 
             		(bind ?candidato1 ?a) 
             		(bind ?candidato2 ?b) 
             		(bind ?candidato3 ?c))
      		(bind ?k (+ ?k 1)))
      (bind ?j (+ ?j 1))
      (bind ?k 1))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidato1))
         (modify ?h3 (rango ?candidato2))
         (modify ?h4 (rango ?candidato3))))
         
         
         
;;;============================================================================
;;; Reglas que resuelven restricciones que aplican a exactamente 4 celdas
;;;============================================================================

;;; Si una restriccion aplica sobre 4 casillas, y tres de ellas estan resueltas
;;; aplicar a la resultante la resta del valor de la restriccion con los dos valores asignados


; La casilla que no está resuelta es la primera:

(defrule 4-casillas-3-resueltas1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  (test (> (length$ $?r1) 1))
  =>
  (bind ?sol (- ?v (+ ?r2 (+ ?r3 ?r4))))
  (if (<= ?sol 9)
    then (modify ?h2 (rango ?sol))))
    
    
    
; La casilla que no está resuelta es la segunda:

(defrule 4-casillas-3-resueltas2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  (test (> (length$ $?r2) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r3 ?r4))))
  (if (<= ?sol 9)
    then (modify ?h3 (rango ?sol))))
    
    
; La casilla que no está resuelta es la tercera:

(defrule 4-casillas-3-resueltas3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  (test (> (length$ $?r3) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r2 ?r4))))
  (if (<= ?sol 9)
    then (modify ?h4 (rango ?sol))))
    
    
    
; La casilla que no está resuelta es la cuarta:

(defrule 4-casillas-3-resueltas4
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango $?r4))
  (test (> (length$ $?r4) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r2 ?r3))))
  (if (<= ?sol 9)
    then (modify ?h5 (rango ?sol))))
    
    
    
;;;============================================================================

;;; Si una restriccion aplica sobre 4 casillas, y dos de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible.


; Resueltas la primera y la segunda casilla:

(defrule 4-casillas-2-resueltas1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  ?h5 <- (celda (id ?c4) (rango $?r4))
  (test (> (length$ $?r3) 1))
  (test (> (length$ $?r4) 1))
  =>
  (bind ?v (- ?v (+ ?r1 ?r2)))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r3))
    (bind ?a (nth$ ?i $?r3))
    (while (<= ?j (length$ $?r4))
      (bind ?b (nth$ ?j $?r4))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h4 (rango ?candidato1))
         (modify ?h5 (rango ?candidato2))))



; Resueltas la primera y la tercera casilla:

(defrule 4-casillas-2-resueltas2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango $?r4))
  (test (> (length$ $?r2) 1))
  (test (> (length$ $?r4) 1))
  =>
  (bind ?v (- ?v (+ ?r1 ?r3)))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r2))
    (bind ?a (nth$ ?i $?r2))
    (while (<= ?j (length$ $?r4))
      (bind ?b (nth$ ?j $?r4))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h3 (rango ?candidato1))
         (modify ?h5 (rango ?candidato2))))
         
         
    
; Resueltas la primera y la cuarta casilla:

(defrule 4-casillas-2-resueltas3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  (test (> (length$ $?r2) 1))
  (test (> (length$ $?r3) 1))
  =>
  (bind ?v (- ?v (+ ?r1 ?r4)))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r2))
    (bind ?a (nth$ ?i $?r2))
    (while (<= ?j (length$ $?r3))
      (bind ?b (nth$ ?j $?r3))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h3 (rango ?candidato1))
         (modify ?h4 (rango ?candidato2))))
         
         
         
         
; Resueltas la segunda y la tercera casilla:

(defrule 4-casillas-2-resueltas4
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango $?r4))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r4) 1))
  =>
  (bind ?v (- ?v (+ ?r2 ?r3)))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r1))
    (bind ?a (nth$ ?i $?r1))
    (while (<= ?j (length$ $?r4))
      (bind ?b (nth$ ?j $?r4))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidato1))
         (modify ?h5 (rango ?candidato2))))
         


; Resueltas la segunda y la cuarta casilla:

(defrule 4-casillas-2-resueltas5
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r3) 1))
  =>
  (bind ?v (- ?v (+ ?r2 ?r4)))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r1))
    (bind ?a (nth$ ?i $?r1))
    (while (<= ?j (length$ $?r3))
      (bind ?b (nth$ ?j $?r3))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidato1))
         (modify ?h4 (rango ?candidato2))))
         
         

; Resueltas la tercera y la cuarta casilla:

(defrule 4-casillas-2-resueltas6
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r2) 1))
  =>
  (bind ?v (- ?v (+ ?r3 ?r4)))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r1))
    (bind ?a (nth$ ?i $?r1))
    (while (<= ?j (length$ $?r2))
      (bind ?b (nth$ ?j $?r2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidato1))
         (modify ?h3 (rango ?candidato2))))
         
         
         
         
;;;============================================================================

;;; Si una restriccion aplica sobre 4 casillas, y una de ellas esta resuelta
;;; probar combinaciones y asingar si solo hay una posible.

; La casilla resuelta es la primera:

(defrule 4-casillas-1-resuelta1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  ?h5 <- (celda (id ?c4) (rango $?r4))
  (test (> (length$ $?r2) 1))
  (test (> (length$ $?r3) 1))
  (test (> (length$ $?r4) 1))
  =>
  (bind ?v (- ?v ?r1))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?candidato3 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?k 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r2))
    (bind ?a (nth$ ?i $?r2))
    (while (<= ?j (length$ $?r3))
      (bind ?b (nth$ ?j $?r3))
      	(while (<= ?k (length$ $?r4))
      		(bind ?c (nth$ ?k $?r4))
      			(if (and (eq ?v (+ ?a (+ ?b ?c))) (neq ?a ?b) (neq ?a ?c) (neq ?b ?c))
        			then
             		(bind ?cont (+ ?cont +1)) 
             		(bind ?candidato1 ?a) 
             		(bind ?candidato2 ?b) 
             		(bind ?candidato3 ?c))
      		(bind ?k (+ ?k 1)))
      (bind ?j (+ ?j 1))
      (bind ?k 1))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h3 (rango ?candidato1))
         (modify ?h4 (rango ?candidato2))
         (modify ?h5 (rango ?candidato3))))
         
         
         
; La casilla resuelta es la segunda:

(defrule 4-casillas-1-resuelta2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  ?h5 <- (celda (id ?c4) (rango $?r4))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r3) 1))
  (test (> (length$ $?r4) 1))
  =>
  (bind ?v (- ?v ?r2))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?candidato3 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?k 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r1))
    (bind ?a (nth$ ?i $?r1))
    (while (<= ?j (length$ $?r3))
      (bind ?b (nth$ ?j $?r3))
      	(while (<= ?k (length$ $?r4))
      		(bind ?c (nth$ ?k $?r4))
      			(if (and (eq ?v (+ ?a (+ ?b ?c))) (neq ?a ?b) (neq ?a ?c) (neq ?b ?c))
        			then
             		(bind ?cont (+ ?cont +1)) 
             		(bind ?candidato1 ?a) 
             		(bind ?candidato2 ?b) 
             		(bind ?candidato3 ?c))
      		(bind ?k (+ ?k 1)))
      (bind ?j (+ ?j 1))
      (bind ?k 1))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidato1))
         (modify ?h4 (rango ?candidato2))
         (modify ?h5 (rango ?candidato3))))



; La casilla resuelta es la tercera:

(defrule 4-casillas-1-resuelta3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango $?r4))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r2) 1))
  (test (> (length$ $?r4) 1))
  =>
  (bind ?v (- ?v ?r3))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?candidato3 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?k 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r1))
    (bind ?a (nth$ ?i $?r1))
    (while (<= ?j (length$ $?r2))
      (bind ?b (nth$ ?j $?r2))
      	(while (<= ?k (length$ $?r4))
      		(bind ?c (nth$ ?k $?r4))
      			(if (and (eq ?v (+ ?a (+ ?b ?c))) (neq ?a ?b) (neq ?a ?c) (neq ?b ?c))
        			then
             		(bind ?cont (+ ?cont +1)) 
             		(bind ?candidato1 ?a) 
             		(bind ?candidato2 ?b) 
             		(bind ?candidato3 ?c))
      		(bind ?k (+ ?k 1)))
      (bind ?j (+ ?j 1))
      (bind ?k 1))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidato1))
         (modify ?h3 (rango ?candidato2))
         (modify ?h5 (rango ?candidato3))))



; La casilla resuelta es la cuarta:

(defrule 4-casillas-1-resuelta4
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r2) 1))
  (test (> (length$ $?r3) 1))
  =>
  (bind ?v (- ?v ?r4))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?candidato3 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?k 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r1))
    (bind ?a (nth$ ?i $?r1))
    (while (<= ?j (length$ $?r2))
      (bind ?b (nth$ ?j $?r2))
      	(while (<= ?k (length$ $?r3))
      		(bind ?c (nth$ ?k $?r3))
      			(if (and (eq ?v (+ ?a (+ ?b ?c))) (neq ?a ?b) (neq ?a ?c) (neq ?b ?c))
        			then
             		(bind ?cont (+ ?cont +1)) 
             		(bind ?candidato1 ?a) 
             		(bind ?candidato2 ?b) 
             		(bind ?candidato3 ?c))
      		(bind ?k (+ ?k 1)))
      (bind ?j (+ ?j 1))
      (bind ?k 1))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidato1))
         (modify ?h3 (rango ?candidato2))
         (modify ?h4 (rango ?candidato3))))
         
         
         
         
         
;;;============================================================================
;;; Reglas que resuelven restricciones que aplican a exactamente 5 celdas
;;;============================================================================

;;; Si una restriccion aplica sobre 5 casillas, y cuatro de ellas estan resueltas
;;; aplicar a la resultante la resta del valor de la restriccion con los valores 
;;; asignados


; La casilla sin resolver es la primera:

(defrule 5-casillas-4-resueltas1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  (test (> (length$ $?r1) 1))
  =>
  (bind ?sol (- ?v (+ ?r2 (+ ?r3 (+ ?r4 ?r5)))))
  (if (<= ?sol 9)
    then (modify ?h2 (rango ?sol))))




; La casilla sin resolver es la segunda:

(defrule 5-casillas-4-resueltas2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  (test (> (length$ $?r2) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r3 (+ ?r4 ?r5)))))
  (if (<= ?sol 9)
    then (modify ?h3 (rango ?sol))))
    
    
    
; La casilla sin resolver es la tercera:

(defrule 5-casillas-4-resueltas3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  (test (> (length$ $?r3) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r2 (+ ?r4 ?r5)))))
  (if (<= ?sol 9)
    then (modify ?h4 (rango ?sol))))
    
    

; La casilla sin resolver es la cuarta:

(defrule 5-casillas-4-resueltas4
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango $?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  (test (> (length$ $?r4) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r2 (+ ?r3 ?r5)))))
  (if (<= ?sol 9)
    then (modify ?h5 (rango ?sol))))
    
    
; La casilla sin resolver es la quinta:

(defrule 5-casillas-4-resueltas5
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango $?r5))
  (test (> (length$ $?r5) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r2 (+ ?r3 ?r4)))))
  (if (<= ?sol 9)
    then (modify ?h6 (rango ?sol))))
    

;;;============================================================================

;;; Si una restriccion aplica sobre 5 casillas, y tres de ellas estan resueltas
;;; probar combinaciones y asingar si solo hay una posible.


; Las resueltas son la 1, 2 y 3:

(defrule 5-casillas-3-resueltas-1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango $?r4))
  ?h6 <- (celda (id ?c5) (rango $?r5))
  (test (> (length$ $?r4) 1))
  (test (> (length$ $?r5) 1))
  =>
  (bind ?v (- ?v (+ ?r1 (+ ?r2 ?r3))))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r4))
    (bind ?a (nth$ ?i $?r4))
    (while (<= ?j (length$ $?r5))
      (bind ?b (nth$ ?j $?r5))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h5 (rango ?candidato1))
         (modify ?h6 (rango ?candidato2))))



; Las resueltas son la 1, 2 y 4:

(defrule 5-casillas-3-resueltas-2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango $?r5))
  (test (> (length$ $?r3) 1))
  (test (> (length$ $?r5) 1))
  =>
  (bind ?v (- ?v (+ ?r1 (+ ?r2 ?r4))))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r3))
    (bind ?a (nth$ ?i $?r3))
    (while (<= ?j (length$ $?r5))
      (bind ?b (nth$ ?j $?r5))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h4 (rango ?candidato1))
         (modify ?h6 (rango ?candidato2))))
         
         
         
; Las resueltas son la 1, 2 y 5:

(defrule 5-casillas-3-resueltas-3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  ?h5 <- (celda (id ?c4) (rango $?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  (test (> (length$ $?r3) 1))
  (test (> (length$ $?r4) 1))
  =>
  (bind ?v (- ?v (+ ?r1 (+ ?r2 ?r5))))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r3))
    (bind ?a (nth$ ?i $?r3))
    (while (<= ?j (length$ $?r4))
      (bind ?b (nth$ ?j $?r4))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h4 (rango ?candidato1))
         (modify ?h5 (rango ?candidato2))))
         
         
         
; Las resueltas son la 1, 3 y 4:

(defrule 5-casillas-3-resueltas-4
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango $?r5))
  (test (> (length$ $?r2) 1))
  (test (> (length$ $?r5) 1))
  =>
  (bind ?v (- ?v (+ ?r1 (+ ?r3 ?r4))))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r2))
    (bind ?a (nth$ ?i $?r2))
    (while (<= ?j (length$ $?r5))
      (bind ?b (nth$ ?j $?r5))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h3 (rango ?candidato1))
         (modify ?h6 (rango ?candidato2))))
         
         
         
; Las resueltas son la 1, 3 y 5:

(defrule 5-casillas-3-resueltas-5
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango $?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  (test (> (length$ $?r2) 1))
  (test (> (length$ $?r4) 1))
  =>
  (bind ?v (- ?v (+ ?r1 (+ ?r3 ?r5))))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r2))
    (bind ?a (nth$ ?i $?r2))
    (while (<= ?j (length$ $?r4))
      (bind ?b (nth$ ?j $?r4))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h3 (rango ?candidato1))
         (modify ?h5 (rango ?candidato2))))



; Las resueltas son la 1, 4 y 5:

(defrule 5-casillas-3-resueltas-6
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  (test (> (length$ $?r2) 1))
  (test (> (length$ $?r3) 1))
  =>
  (bind ?v (- ?v (+ ?r1 (+ ?r4 ?r5))))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r2))
    (bind ?a (nth$ ?i $?r2))
    (while (<= ?j (length$ $?r3))
      (bind ?b (nth$ ?j $?r3))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h3 (rango ?candidato1))
         (modify ?h4 (rango ?candidato2))))



; Las resueltas son la 2, 3 y 4:

(defrule 5-casillas-3-resueltas-7
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango $?r5))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r5) 1))
  =>
  (bind ?v (- ?v (+ ?r2 (+ ?r3 ?r4))))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r1))
    (bind ?a (nth$ ?i $?r1))
    (while (<= ?j (length$ $?r5))
      (bind ?b (nth$ ?j $?r5))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidato1))
         (modify ?h6 (rango ?candidato2))))
         
         

; Las resueltas son la 2, 3 y 5:

(defrule 5-casillas-3-resueltas-8
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango $?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r4) 1))
  =>
  (bind ?v (- ?v (+ ?r2 (+ ?r3 ?r5))))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r1))
    (bind ?a (nth$ ?i $?r1))
    (while (<= ?j (length$ $?r4))
      (bind ?b (nth$ ?j $?r4))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidato1))
         (modify ?h5 (rango ?candidato2))))
         
         
         
         

; Las resueltas son la 2, 4 y 5:

(defrule 5-casillas-3-resueltas-9
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r3) 1))
  =>
  (bind ?v (- ?v (+ ?r2 (+ ?r4 ?r5))))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r1))
    (bind ?a (nth$ ?i $?r1))
    (while (<= ?j (length$ $?r3))
      (bind ?b (nth$ ?j $?r3))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidato1))
         (modify ?h4 (rango ?candidato2))))
         
         
         
         
; Las resueltas son la 3, 4 y 5:

(defrule 5-casillas-3-resueltas-10
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  (test (> (length$ $?r1) 1))
  (test (> (length$ $?r2) 1))
  =>
  (bind ?v (- ?v (+ ?r3 (+ ?r4 ?r5))))
  (bind ?candidato1 0)
  (bind ?candidato2 0)
  (bind ?i 1)
  (bind ?j 1)
  (bind ?cont 0)
  (while (<= ?i (length$ $?r1))
    (bind ?a (nth$ ?i $?r1))
    (while (<= ?j (length$ $?r2))
      (bind ?b (nth$ ?j $?r2))
      (if (and (eq ?v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?cont (+ ?cont +1)) 
             (bind ?candidato1 ?a) 
             (bind ?candidato2 ?b))
      (bind ?j (+ ?j 1)))
    (bind ?i (+ ?i 1))
    (bind ?j 1))
  (if (eq ?cont 1)
    then (modify ?h2 (rango ?candidato1))
         (modify ?h3 (rango ?candidato2))))
         
         



;;;============================================================================
;;; Reglas que resuelven restricciones que aplican a exactamente 6 celdas
;;;============================================================================

;;; Si una restriccion aplica sobre 6 casillas, y una de ellas no esta 
;;; resueltas, por tanto, resolver aplicando la resta a la restriccion del
;;; total de sumar el resto de elementos.


; La casilla no resuelta es la 1:

(defrule 6-casillas-5-resueltas1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  ?h7 <- (celda (id ?c6) (rango ?r6))
  (test (> (length$ $?r1) 1))
  =>
  (bind ?sol (- ?v (+ ?r2 (+ ?r3 (+ ?r4 (+ ?r5 ?r6))))))
  (if (<= ?sol 9)
    then (modify ?h2 (rango ?sol))))





; La casilla no resuelta es la 2:

(defrule 6-casillas-5-resueltas2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  ?h7 <- (celda (id ?c6) (rango ?r6))
  (test (> (length$ $?r2) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r3 (+ ?r4 (+ ?r5 ?r6))))))
  (if (<= ?sol 9)
    then (modify ?h3 (rango ?sol))))
    
    
    
; La casilla no resuelta es la 3:

(defrule 6-casillas-5-resueltas3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  ?h7 <- (celda (id ?c6) (rango ?r6))
  (test (> (length$ $?r3) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r2 (+ ?r4 (+ ?r5 ?r6))))))
  (if (<= ?sol 9)
    then (modify ?h4 (rango ?sol))))
    
    
    
; La casilla no resuelta es la 4:

(defrule 6-casillas-5-resueltas4
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango $?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  ?h7 <- (celda (id ?c6) (rango ?r6))
  (test (> (length$ $?r4) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r2 (+ ?r3 (+ ?r5 ?r6))))))
  (if (<= ?sol 9)
    then (modify ?h5 (rango ?sol))))
    
    
    
; La casilla no resuelta es la 5:

(defrule 6-casillas-5-resueltas5
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango $?r5))
  ?h7 <- (celda (id ?c6) (rango ?r6))
  (test (> (length$ $?r5) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r2 (+ ?r3 (+ ?r4 ?r6))))))
  (if (<= ?sol 9)
    then (modify ?h6 (rango ?sol))))
    
    
    
; La casilla no resuelta es la 6:

(defrule 6-casillas-5-resueltas6
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  ?h7 <- (celda (id ?c6) (rango $?r6))
  (test (> (length$ $?r6) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r2 (+ ?r3 (+ ?r4 ?r5))))))
  (if (<= ?sol 9)
    then (modify ?h7 (rango ?sol))))
    
    
    
    
;;;============================================================================
;;; Reglas que resuelven restricciones que aplican a exactamente 7 celdas
;;;============================================================================

;;; Si una restriccion aplica sobre 7 casillas, y una de ellas no esta 
;;; resueltas, por tanto, resolver aplicando la resta a la restriccion del
;;; total de sumar el resto de elementos.


; La casilla sin resolver es la 1:

(defrule 7-casillas-6-resueltas1
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?c1) (rango $?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  ?h7 <- (celda (id ?c6) (rango ?r6))
  ?h8 <- (celda (id ?c7) (rango ?r7))
  (test (> (length$ $?r1) 1))
  =>
  (bind ?sol (- ?v (+ ?r2 (+ ?r3 (+ ?r4 (+ ?r5 (+ ?r6 ?r7)))))))
  (if (<= ?sol 9)
    then (modify ?h2 (rango ?sol))))




; La casilla sin resolver es la 2:

(defrule 7-casillas-6-resueltas2
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango $?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  ?h7 <- (celda (id ?c6) (rango ?r6))
  ?h8 <- (celda (id ?c7) (rango ?r7))
  (test (> (length$ $?r2) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r3 (+ ?r4 (+ ?r5 (+ ?r6 ?r7)))))))
  (if (<= ?sol 9)
    then (modify ?h3 (rango ?sol))))




; La casilla sin resolver es la 3:

(defrule 7-casillas-6-resueltas3
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango $?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  ?h7 <- (celda (id ?c6) (rango ?r6))
  ?h8 <- (celda (id ?c7) (rango ?r7))
  (test (> (length$ $?r3) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r2 (+ ?r4 (+ ?r5 (+ ?r6 ?r7)))))))
  (if (<= ?sol 9)
    then (modify ?h4 (rango ?sol))))
    
    
    
    
; La casilla sin resolver es la 4:

(defrule 7-casillas-6-resueltas4
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango $?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  ?h7 <- (celda (id ?c6) (rango ?r6))
  ?h8 <- (celda (id ?c7) (rango ?r7))
  (test (> (length$ $?r4) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r2 (+ ?r3 (+ ?r5 (+ ?r6 ?r7)))))))
  (if (<= ?sol 9)
    then (modify ?h5 (rango ?sol))))
    
    
    
; La casilla sin resolver es la 5:

(defrule 7-casillas-6-resueltas5
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango $?r5))
  ?h7 <- (celda (id ?c6) (rango ?r6))
  ?h8 <- (celda (id ?c7) (rango ?r7))
  (test (> (length$ $?r5) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r2 (+ ?r3 (+ ?r4 (+ ?r6 ?r7)))))))
  (if (<= ?sol 9)
    then (modify ?h6 (rango ?sol))))
    
    
    
    
; La casilla sin resolver es la 6:

(defrule 7-casillas-6-resueltas6
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  ?h7 <- (celda (id ?c6) (rango $?r6))
  ?h8 <- (celda (id ?c7) (rango ?r7))
  (test (> (length$ $?r6) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r2 (+ ?r3 (+ ?r4 (+ ?r5 ?r7)))))))
  (if (<= ?sol 9)
    then (modify ?h7 (rango ?sol))))
    
    
    
   
; La casilla sin resolver es la 7:

(defrule 7-casillas-6-resueltas7
  (declare (salience -8))
  ?h1 <- (restriccion (valor ?v) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?c1) (rango ?r1))
  ?h3 <- (celda (id ?c2) (rango ?r2))
  ?h4 <- (celda (id ?c3) (rango ?r3))
  ?h5 <- (celda (id ?c4) (rango ?r4))
  ?h6 <- (celda (id ?c5) (rango ?r5))
  ?h7 <- (celda (id ?c6) (rango ?r6))
  ?h8 <- (celda (id ?c7) (rango $?r7))
  (test (> (length$ $?r7) 1))
  =>
  (bind ?sol (- ?v (+ ?r1 (+ ?r2 (+ ?r3 (+ ?r4 (+ ?r5 ?r6)))))))
  (if (<= ?sol 9)
    then (modify ?h8 (rango ?sol))))
    
    
    
    
    
;;;============================================================================
;;; Reglas que aplican en bloques magicos
;;;============================================================================

;;; Reglas para encontrar bloques magicos, que son bloques que nos ayudan a
;;; eliminar candidatos y encontrar posibilidades de resolucion con 
;;; reglas de interseccion

;;; BM - Elimina valor distintos de 1 y 2 para celdas con restriccion 3 y
;;; numero de casillas 2


(defrule suma3-2casillas-1y2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 3)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (neq ?r 1) (neq ?r 2)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (neq ?r1 1) (neq ?r1 2)) $?w1))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1)))




;;; BM - Elimina valor distintos de 1 y 3 para celdas con restriccion 4 y
;;; numero de casillas 2


(defrule suma4-2casillas-1y3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 4)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (neq ?r 1) (neq ?r 3)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (neq ?r1 1) (neq ?r1 3)) $?w1))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1)))



;;; BM - Elimina valor distintos de 7 y 9 para celdas con restriccion 16 y
;;; numero de casillas 2


(defrule suma16-2casillas-7y9
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 16)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (neq ?r 7) (neq ?r 9)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (neq ?r1 7) (neq ?r1 9)) $?w1))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1)))



;;; BM - Elimina valor distintos de 8 y 9 para celdas con restriccion 17 y
;;; numero de casillas 2


(defrule suma17-2casillas-8y9
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 17)) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (neq ?r 8) (neq ?r 9)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (neq ?r1 8) (neq ?r1 9)) $?w1))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1)))
  
  

;;; BM - Elimina valor distintos de 1, 2 y 3 para celdas con restriccion 6 y
;;; numero de casillas 3


(defrule suma6-3casillas-1y2y3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 6)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (neq ?r 1) (and (neq ?r 2) (neq ?r 3))) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (neq ?r1 1) (and (neq ?r1 2) (neq ?r1 3))) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(and (neq ?r2 1) (and (neq ?r2 2) (neq ?r2 3))) $?w2))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2)))




;;; BM - Elimina valor distintos de 1, 2 y 4 para celdas con restriccion 7 y
;;; numero de casillas 3


(defrule suma7-3casillas-1y2y4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 7)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (neq ?r 1) (and (neq ?r 2) (neq ?r 4))) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (neq ?r1 1) (and (neq ?r1 2) (neq ?r1 4))) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(and (neq ?r2 1) (and (neq ?r2 2) (neq ?r2 4))) $?w2))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2)))


;;; BM - Elimina valor distintos de 6, 8 y 9 para celdas con restriccion 23 y
;;; numero de casillas 3


(defrule suma23-3casillas-6y8y9
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 23)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (neq ?r 6) (and (neq ?r 8) (neq ?r 9))) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (neq ?r1 6) (and (neq ?r1 8) (neq ?r1 9))) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(and (neq ?r2 6) (and (neq ?r2 8) (neq ?r2 9))) $?w2))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2)))




;;; BM - Elimina valor distintos de 7, 8 y 9 para celdas con restriccion 24 y
;;; numero de casillas 3


(defrule suma24-3casillas-7y8y9
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 24)) (casillas ?c1 ?c2 ?c3))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (neq ?r 7) (and (neq ?r 8) (neq ?r 9))) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (neq ?r1 7) (and (neq ?r1 8) (neq ?r1 9))) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(and (neq ?r2 7) (and (neq ?r2 8) (neq ?r2 9))) $?w2))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2)))


;;; BM - Elimina valor distintos de 1, 2, 3 y 4 para celdas con restriccion 10 y
;;; numero de casillas 4


(defrule suma10-4casillas-1y2y3y4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 10)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (and (neq ?r 1) (neq ?r 2)) (and (neq ?r 3) (neq ?r 4))) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (and (neq ?r1 1) (neq ?r1 2)) (and (neq ?r1 3) (neq ?r1 4))) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(and (and (neq ?r2 1) (neq ?r2 2)) (and (neq ?r2 3) (neq ?r2 4))) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(and (and (neq ?r3 1) (neq ?r3 2)) (and (neq ?r3 3) (neq ?r3 4))) $?w3))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3)))



;;; BM - Elimina valor distintos de 1, 2, 3 y 5 para celdas con restriccion 11 y
;;; numero de casillas 4


(defrule suma11-4casillas-1y2y3y5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 11)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (and (neq ?r 1) (neq ?r 2)) (and (neq ?r 3) (neq ?r 5))) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (and (neq ?r1 1) (neq ?r1 2)) (and (neq ?r1 3) (neq ?r1 5))) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(and (and (neq ?r2 1) (neq ?r2 2)) (and (neq ?r2 3) (neq ?r2 5))) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(and (and (neq ?r3 1) (neq ?r3 2)) (and (neq ?r3 3) (neq ?r3 5))) $?w3))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3)))


;;; BM - Elimina valor distintos de 5, 7, 8 y 9 para celdas con restriccion 29 y
;;; numero de casillas 4


(defrule suma29-4casillas-5y7y8y9
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 29)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (and (neq ?r 5) (neq ?r 7)) (and (neq ?r 8) (neq ?r 9))) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (and (neq ?r1 5) (neq ?r1 7)) (and (neq ?r1 8) (neq ?r1 9))) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(and (and (neq ?r2 5) (neq ?r2 7)) (and (neq ?r2 8) (neq ?r2 9))) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(and (and (neq ?r3 5) (neq ?r3 7)) (and (neq ?r3 8) (neq ?r3 9))) $?w3))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3)))


;;; BM - Elimina valor distintos de 6, 7, 8 y 9 para celdas con restriccion 30 y
;;; numero de casillas 4

(defrule suma29-4casillas-6y7y8y9
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 30)) (casillas ?c1 ?c2 ?c3 ?c4))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (and (neq ?r 6) (neq ?r 7)) (and (neq ?r 8) (neq ?r 9))) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (and (neq ?r1 6) (neq ?r1 7)) (and (neq ?r1 8) (neq ?r1 9))) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(and (and (neq ?r2 6) (neq ?r2 7)) (and (neq ?r2 8) (neq ?r2 9))) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(and (and (neq ?r3 6) (neq ?r3 7)) (and (neq ?r3 8) (neq ?r3 9))) $?w3))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3)))



;;; BM - Elimina valor distintos de 1, 2, 3, 4 y 5 para celdas con restriccion 15 y
;;; numero de casillas 5


(defrule suma15-5casillas-1y2y3y4y5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 15)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4) (neq ?r 5)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (neq ?r1 1) (neq ?r1 2) (neq ?r1 3) (neq ?r1 4) (neq ?r1 5)) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(and (neq ?r2 1) (neq ?r2 2) (neq ?r2 3) (neq ?r2 4) (neq ?r2 5)) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(and (neq ?r3 1) (neq ?r3 2) (neq ?r3 3) (neq ?r3 4) (neq ?r3 5)) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(and (neq ?r4 1) (neq ?r4 2) (neq ?r4 3) (neq ?r4 4) (neq ?r4 5)) $?w4))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4)))



;;; BM - Elimina valor distintos de 1, 2, 3, 4 y 6 para celdas con restriccion 16 y
;;; numero de casillas 5

(defrule suma16-5casillas-1y2y3y4y6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 16)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (neq ?r 1) (neq ?r 2) (neq ?r 3) (neq ?r 4) (neq ?r 6)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (neq ?r1 1) (neq ?r1 2) (neq ?r1 3) (neq ?r1 4) (neq ?r1 6)) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(and (neq ?r2 1) (neq ?r2 2) (neq ?r2 3) (neq ?r2 4) (neq ?r2 6)) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(and (neq ?r3 1) (neq ?r3 2) (neq ?r3 3) (neq ?r3 4) (neq ?r3 6)) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(and (neq ?r4 1) (neq ?r4 2) (neq ?r4 3) (neq ?r4 4) (neq ?r4 6)) $?w4))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4)))




;;; BM - Elimina valor distintos de 4, 6, 7, 8 y 9 para celdas con restriccion 34 y
;;; numero de casillas 5


(defrule suma34-5casillas-4y6y7y8y9
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 16)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (neq ?r 4) (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (neq ?r1 4) (neq ?r1 6) (neq ?r1 7) (neq ?r1 8) (neq ?r1 9)) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(and (neq ?r2 4) (neq ?r2 6) (neq ?r2 7) (neq ?r2 8) (neq ?r2 9)) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(and (neq ?r3 4) (neq ?r3 6) (neq ?r3 7) (neq ?r3 8) (neq ?r3 9)) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(and (neq ?r4 4) (neq ?r4 6) (neq ?r4 7) (neq ?r4 8) (neq ?r4 9)) $?w4))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4)))



;;; BM - Elimina valor distintos de 5, 6, 7, 8 y 9 para celdas con restriccion 35 y
;;; numero de casillas 5



(defrule suma35-5casillas-5y6y7y8y9
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 35)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(and (neq ?r 5) (neq ?r 6) (neq ?r 7) (neq ?r 8) (neq ?r 9)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(and (neq ?r1 5) (neq ?r1 6) (neq ?r1 7) (neq ?r1 8) (neq ?r1 9)) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(and (neq ?r2 5) (neq ?r2 6) (neq ?r2 7) (neq ?r2 8) (neq ?r2 9)) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(and (neq ?r3 5) (neq ?r3 6) (neq ?r3 7) (neq ?r3 8) (neq ?r3 9)) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(and (neq ?r4 5) (neq ?r4 6) (neq ?r4 7) (neq ?r4 8) (neq ?r4 9)) $?w4))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4)))




;;; BM - Eliminar valor 7, 8 o 9 para celdas con restriccion 21 y numero de casillas 6


(defrule suma21-6casillas-elimina7y8y9
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 21)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(or (eq ?r 7) (eq ?r 8) (eq ?r 9)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(or (eq ?r1 7) (eq ?r1 8) (eq ?r1 9)) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(or (eq ?r2 7) (eq ?r2 8) (eq ?r2 9)) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(or (eq ?r3 7) (eq ?r3 8) (eq ?r3 9)) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(or (eq ?r4 7) (eq ?r4 8) (eq ?r4 9)) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(or (eq ?r5 7) (eq ?r5 8) (eq ?r5 9)) $?w5))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5)))





;;; BM - Eliminar valor 6, 8 o 9 para celdas con restriccion 22 y numero de casillas 6


(defrule suma22-6casillas-elimina6y8y9
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 22)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(or (eq ?r 6) (eq ?r 8) (eq ?r 9)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(or (eq ?r1 6) (eq ?r1 8) (eq ?r1 9)) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(or (eq ?r2 6) (eq ?r2 8) (eq ?r2 9)) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(or (eq ?r3 6) (eq ?r3 8) (eq ?r3 9)) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(or (eq ?r4 6) (eq ?r4 8) (eq ?r4 9)) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(or (eq ?r5 6) (eq ?r5 8) (eq ?r5 9)) $?w5))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5)))




;;; BM - Eliminar valor 1, 2 o 4 para celdas con restriccion 38 y numero de casillas 6


(defrule suma38-6casillas-elimina1y2y4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(or (eq ?r 1) (eq ?r 2) (eq ?r 4)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(or (eq ?r1 1) (eq ?r1 2) (eq ?r1 4)) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(or (eq ?r2 1) (eq ?r2 2) (eq ?r2 4)) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(or (eq ?r3 1) (eq ?r3 2) (eq ?r3 4)) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(or (eq ?r4 1) (eq ?r4 2) (eq ?r4 4)) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(or (eq ?r5 1) (eq ?r5 2) (eq ?r5 4)) $?w5))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5)))


;;; BM - Eliminar valor 1, 2 o 3 para celdas con restriccion 39 y numero de casillas 6


(defrule suma39-6casillas-elimina1y2y3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(or (eq ?r 1) (eq ?r 2) (eq ?r 3)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(or (eq ?r1 1) (eq ?r1 2) (eq ?r1 3)) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(or (eq ?r2 1) (eq ?r2 2) (eq ?r2 3)) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(or (eq ?r3 1) (eq ?r3 2) (eq ?r3 3)) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(or (eq ?r4 1) (eq ?r4 2) (eq ?r4 3)) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(or (eq ?r5 1) (eq ?r5 2) (eq ?r5 3)) $?w5))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5)))



;;; BM - Eliminar valor 8 o 9 para celdas con restriccion 28 y numero de casillas 7


(defrule suma28-7casillas-elimina8y9
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 28)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(or (eq ?r 8) (eq ?r 9)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(or (eq ?r1 8) (eq ?r1 9)) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(or (eq ?r2 8) (eq ?r2 9)) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(or (eq ?r3 8) (eq ?r3 9)) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(or (eq ?r4 8) (eq ?r4 9)) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(or (eq ?r5 8) (eq ?r5 9)) $?w5))
  ?h8 <- (celda (id ?c7) (rango $?u6 ?r6&:(or (eq ?r6 8) (eq ?r6 9)) $?w6))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  (test (or (> (length$ $?u6) 0)(> (length$ $?w6) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5))
  (modify ?h8 (rango $?u6 $?w6)))




;;; BM - Eliminar valor 7 o 9 para celdas con restriccion 29 y numero de casillas 7


(defrule suma29-7casillas-elimina7y9
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 29)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(or (eq ?r 7) (eq ?r 9)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(or (eq ?r1 7) (eq ?r1 9)) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(or (eq ?r2 7) (eq ?r2 9)) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(or (eq ?r3 7) (eq ?r3 9)) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(or (eq ?r4 7) (eq ?r4 9)) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(or (eq ?r5 7) (eq ?r5 9)) $?w5))
  ?h8 <- (celda (id ?c7) (rango $?u6 ?r6&:(or (eq ?r6 7) (eq ?r6 9)) $?w6))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  (test (or (> (length$ $?u6) 0)(> (length$ $?w6) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5))
  (modify ?h8 (rango $?u6 $?w6)))



;;; BM - Eliminar valor 1 o 3 para celdas con restriccion 41 y numero de casillas 7


(defrule suma41-7casillas-elimina1y3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(or (eq ?r 1) (eq ?r 3)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(or (eq ?r1 1) (eq ?r1 3)) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(or (eq ?r2 1) (eq ?r2 3)) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(or (eq ?r3 1) (eq ?r3 3)) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(or (eq ?r4 1) (eq ?r4 3)) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(or (eq ?r5 1) (eq ?r5 3)) $?w5))
  ?h8 <- (celda (id ?c7) (rango $?u6 ?r6&:(or (eq ?r6 1) (eq ?r6 3)) $?w6))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  (test (or (> (length$ $?u6) 0)(> (length$ $?w6) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5))
  (modify ?h8 (rango $?u6 $?w6)))



;;; BM - Eliminar valor 1 o 2 para celdas con restriccion 42 y numero de casillas 7


(defrule suma42-7casillas-elimina1y2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(or (eq ?r 1) (eq ?r 2)) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(or (eq ?r1 1) (eq ?r1 2)) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(or (eq ?r2 1) (eq ?r2 2)) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(or (eq ?r3 1) (eq ?r3 2)) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(or (eq ?r4 1) (eq ?r4 2)) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(or (eq ?r5 1) (eq ?r5 2)) $?w5))
  ?h8 <- (celda (id ?c7) (rango $?u6 ?r6&:(or (eq ?r6 1) (eq ?r6 2)) $?w6))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  (test (or (> (length$ $?u6) 0)(> (length$ $?w6) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5))
  (modify ?h8 (rango $?u6 $?w6)))



;;; BM - Eliminar valor 9 para celdas con restriccion 36 y numero de casillas 8

(defrule suma36-8casillas-elimina9
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 36)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(eq ?r 9) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(eq ?r1 9) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(eq ?r2 9) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(eq ?r3 9) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(eq ?r4 9) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(eq ?r5 9) $?w5))
  ?h8 <- (celda (id ?c7) (rango $?u6 ?r6&:(eq ?r6 9) $?w6))
  ?h9 <- (celda (id ?c8) (rango $?u7 ?r7&:(eq ?r7 9) $?w7))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  (test (or (> (length$ $?u6) 0)(> (length$ $?w6) 0)))
  (test (or (> (length$ $?u7) 0)(> (length$ $?w7) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5))
  (modify ?h8 (rango $?u6 $?w6))
  (modify ?h9 (rango $?u7 $?w7)))



;;; BM - Eliminar valor 8 para celdas con restriccion 37 y numero de casillas 8


(defrule suma37-8casillas-elimina8
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 37)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(eq ?r 8) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(eq ?r1 8) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(eq ?r2 8) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(eq ?r3 8) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(eq ?r4 8) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(eq ?r5 8) $?w5))
  ?h8 <- (celda (id ?c7) (rango $?u6 ?r6&:(eq ?r6 8) $?w6))
  ?h9 <- (celda (id ?c8) (rango $?u7 ?r7&:(eq ?r7 8) $?w7))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  (test (or (> (length$ $?u6) 0)(> (length$ $?w6) 0)))
  (test (or (> (length$ $?u7) 0)(> (length$ $?w7) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5))
  (modify ?h8 (rango $?u6 $?w6))
  (modify ?h9 (rango $?u7 $?w7)))





;;; BM - Eliminar valor 7 para celdas con restriccion 38 y numero de casillas 8



(defrule suma38-8casillas-elimina7
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 38)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(eq ?r 7) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(eq ?r1 7) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(eq ?r2 7) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(eq ?r3 7) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(eq ?r4 7) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(eq ?r5 7) $?w5))
  ?h8 <- (celda (id ?c7) (rango $?u6 ?r6&:(eq ?r6 7) $?w6))
  ?h9 <- (celda (id ?c8) (rango $?u7 ?r7&:(eq ?r7 7) $?w7))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  (test (or (> (length$ $?u6) 0)(> (length$ $?w6) 0)))
  (test (or (> (length$ $?u7) 0)(> (length$ $?w7) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5))
  (modify ?h8 (rango $?u6 $?w6))
  (modify ?h9 (rango $?u7 $?w7)))




;;; BM - Eliminar valor 6 para celdas con restriccion 39 y numero de casillas 8



(defrule suma39-8casillas-elimina6
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 39)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(eq ?r 6) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(eq ?r1 6) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(eq ?r2 6) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(eq ?r3 6) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(eq ?r4 6) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(eq ?r5 6) $?w5))
  ?h8 <- (celda (id ?c7) (rango $?u6 ?r6&:(eq ?r6 6) $?w6))
  ?h9 <- (celda (id ?c8) (rango $?u7 ?r7&:(eq ?r7 6) $?w7))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  (test (or (> (length$ $?u6) 0)(> (length$ $?w6) 0)))
  (test (or (> (length$ $?u7) 0)(> (length$ $?w7) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5))
  (modify ?h8 (rango $?u6 $?w6))
  (modify ?h9 (rango $?u7 $?w7)))





;;; BM - Eliminar valor 5 para celdas con restriccion 40 y numero de casillas 8


(defrule suma40-8casillas-elimina5
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 36)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(eq ?r 5) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(eq ?r1 5) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(eq ?r2 5) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(eq ?r3 5) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(eq ?r4 5) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(eq ?r5 5) $?w5))
  ?h8 <- (celda (id ?c7) (rango $?u6 ?r6&:(eq ?r6 5) $?w6))
  ?h9 <- (celda (id ?c8) (rango $?u7 ?r7&:(eq ?r7 5) $?w7))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  (test (or (> (length$ $?u6) 0)(> (length$ $?w6) 0)))
  (test (or (> (length$ $?u7) 0)(> (length$ $?w7) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5))
  (modify ?h8 (rango $?u6 $?w6))
  (modify ?h9 (rango $?u7 $?w7)))





;;; BM - Eliminar valor 4 para celdas con restriccion 41 y numero de casillas 8




(defrule suma41-8casillas-elimina4
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 41)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(eq ?r 4) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(eq ?r1 4) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(eq ?r2 4) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(eq ?r3 4) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(eq ?r4 4) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(eq ?r5 4) $?w5))
  ?h8 <- (celda (id ?c7) (rango $?u6 ?r6&:(eq ?r6 4) $?w6))
  ?h9 <- (celda (id ?c8) (rango $?u7 ?r7&:(eq ?r7 4) $?w7))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  (test (or (> (length$ $?u6) 0)(> (length$ $?w6) 0)))
  (test (or (> (length$ $?u7) 0)(> (length$ $?w7) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5))
  (modify ?h8 (rango $?u6 $?w6))
  (modify ?h9 (rango $?u7 $?w7)))







;;; BM - Eliminar valor 3 para celdas con restriccion 42 y numero de casillas 8



(defrule suma42-8casillas-elimina3
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 42)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(eq ?r 3) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(eq ?r1 3) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(eq ?r2 3) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(eq ?r3 3) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(eq ?r4 3) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(eq ?r5 3) $?w5))
  ?h8 <- (celda (id ?c7) (rango $?u6 ?r6&:(eq ?r6 3) $?w6))
  ?h9 <- (celda (id ?c8) (rango $?u7 ?r7&:(eq ?r7 3) $?w7))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  (test (or (> (length$ $?u6) 0)(> (length$ $?w6) 0)))
  (test (or (> (length$ $?u7) 0)(> (length$ $?w7) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5))
  (modify ?h8 (rango $?u6 $?w6))
  (modify ?h9 (rango $?u7 $?w7)))





;;; BM - Eliminar valor 2 para celdas con restriccion 43 y numero de casillas 8



(defrule suma43-8casillas-elimina2
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 43)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(eq ?r 2) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(eq ?r1 2) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(eq ?r2 2) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(eq ?r3 2) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(eq ?r4 2) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(eq ?r5 2) $?w5))
  ?h8 <- (celda (id ?c7) (rango $?u6 ?r6&:(eq ?r6 2) $?w6))
  ?h9 <- (celda (id ?c8) (rango $?u7 ?r7&:(eq ?r7 2) $?w7))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  (test (or (> (length$ $?u6) 0)(> (length$ $?w6) 0)))
  (test (or (> (length$ $?u7) 0)(> (length$ $?w7) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5))
  (modify ?h8 (rango $?u6 $?w6))
  (modify ?h9 (rango $?u7 $?w7)))




;;; BM - Eliminar valor 1 para celdas con restriccion 44 y numero de casillas 8



(defrule suma44-8casillas-elimina1
  (declare (salience 70))
  ?h1 <- (restriccion (valor ?v&:(eq ?v 44)) (casillas ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7 ?c8))
  ?h2 <- (celda (id ?c1) (rango $?u ?r&:(eq ?r 1) $?w))
  ?h3 <- (celda (id ?c2) (rango $?u1 ?r1&:(eq ?r1 1) $?w1))
  ?h4 <- (celda (id ?c3) (rango $?u2 ?r2&:(eq ?r2 1) $?w2))
  ?h5 <- (celda (id ?c4) (rango $?u3 ?r3&:(eq ?r3 1) $?w3))
  ?h6 <- (celda (id ?c5) (rango $?u4 ?r4&:(eq ?r4 1) $?w4))
  ?h7 <- (celda (id ?c6) (rango $?u5 ?r5&:(eq ?r5 1) $?w5))
  ?h8 <- (celda (id ?c7) (rango $?u6 ?r6&:(eq ?r6 1) $?w6))
  ?h9 <- (celda (id ?c8) (rango $?u7 ?r7&:(eq ?r7 1) $?w7))
  (test (or (> (length$ $?u) 0)(> (length$ $?w) 0)))
  (test (or (> (length$ $?u1) 0)(> (length$ $?w1) 0)))
  (test (or (> (length$ $?u2) 0)(> (length$ $?w2) 0)))
  (test (or (> (length$ $?u3) 0)(> (length$ $?w3) 0)))
  (test (or (> (length$ $?u4) 0)(> (length$ $?w4) 0)))
  (test (or (> (length$ $?u5) 0)(> (length$ $?w5) 0)))
  (test (or (> (length$ $?u6) 0)(> (length$ $?w6) 0)))
  (test (or (> (length$ $?u7) 0)(> (length$ $?w7) 0)))
  =>
  (modify ?h2 (rango $?u $?w))
  (modify ?h3 (rango $?u1 $?w1))
  (modify ?h4 (rango $?u2 $?w2))
  (modify ?h5 (rango $?u3 $?w3))
  (modify ?h6 (rango $?u4 $?w4))
  (modify ?h7 (rango $?u5 $?w5))
  (modify ?h8 (rango $?u6 $?w6))
  (modify ?h9 (rango $?u7 $?w7)))



