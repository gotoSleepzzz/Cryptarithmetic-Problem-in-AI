from random import choice, randint
from threading import Semaphore
from typing import Counter
from threading import Thread
import copy

inner_population = [] 
inner_population_val = []

obj_1 = Semaphore(1)
obj_2 = Semaphore(0)
obj_3 = Semaphore(1)

count_thread = 0

#oke
def handle_data(s):
  array = []
  for i in range(0, 26):
    array.append(0)

  for i in s:
    tempt = ord(i) - 65
    if (tempt >= 0) and (tempt <= 25):
      array[tempt] = 1
  
  result1 = []
  for i in range(0, 26):
    if (array[i] == 1):
      result1.append(chr(i + 65))

  result2 = s.replace("=","-")

  return result1, result2

#oke
def check_constraint(data, value):
  for i in data:
    if (value == i):
      return True
  
  return False

#oke
def random_Population(constraint, L):
  Result = ['_'] * 10
  List_random = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  count = -1
  
  while (True):
    count = count + 1
    check = check_constraint(constraint, L[count])

    # for random
    while (True):
      val = choice(List_random)
      if (val == 0 and check == True and count == len(L) - 1 and len(L) == 10):
        while (True):
          v = randint(0, 9)
          c = check_constraint(constraint, L[v])
          if (not c):
            break
        # exchange
        Result[val] = Result[v]
        Result[v] = L[count]
        break
      elif (not (val == 0 and check == True)):
        Result[val] = L[count]
        List_random.remove(val)
        break

    if (count == len(L) - 1):
        break
  return Result

#oke
def determine_constraint(data):
  list = []

  list.append(data[0])
  for i in range(0, len(data)):
    if (data[i] == '+' or data[i] == '-' or data[i] == '*' ):
      list.append(data[i + 1])
  
  return list

#oke
def calculate_fitness(List, expression):
  for i in range(0, 10):
    if (List[i] != '_'):
      expression = expression.replace(List[i], str(i))
  
  return abs(eval(expression))
#oke
def check_constraint_exchange(v1, v2, constraint, list):
  if (v1 == v2):
    return False
  if (v1 != 0 and v2 != 0):
    return True
  
  if (v1 == 0):
    # check list[v2] : determine that list[v2] is located in list_constraint
    for i in constraint:
      if (list[v2] == i):
        return False

  if (v2 == 0):
    # check list[v1]
    for i in constraint:
      if (list[v1] == i):
        return False
  
  return True
  
def sub_thread(List, constraint, L, expression,k):
  global inner_population
  global inner_population_val
  global count_thread

  if (len(List) == 0):
    while (True):
      List = random_Population(constraint, L)
      if (check_constraint(constraint, List[0]) == False):
        break
  
  # making new generation from 1 => 100, 50
  for count in range(0, 400):
    obj_1.acquire()
    while (True):
      v1 = randint(0, 9)
      v2 = randint(0, 9)
      if (check_constraint_exchange(v1, v2, list_constraint, List)):
        break
    
    
    tempt = copy.deepcopy(List)
    ka = copy.deepcopy(List)

    # exchange
    t = "_"
    t = tempt[v1] 
    tempt[v1] = tempt[v2]
    tempt[v2] = t

    # calculate the fitness | A + B - C|
    try:
      val = calculate_fitness(tempt,expression)
    except:
      print("List: ", List)
      print("tempt: ", tempt)
      print("Ka: ",  ka)
      print("T: ", k)
      print("V1: ", v1, "  V2: ", v2)
    
    val = calculate_fitness(tempt,expression)
    
    for i in range(0, 20):
      if (inner_population_val[i] == -1):
        # gan inner_opulation[i] = tempt
        for k in range(0, 10):
          inner_population[i][k] = tempt[k]
        inner_population_val[i] = val
        break
      elif (inner_population_val[i] >= val):
        #exchange
        for j in range(19, i, -1):
          if (inner_population_val[j - 1] != -1):
            for k in range(0, 10):
              inner_population[j][k]  = inner_population[j - 1][k]
            inner_population_val[j] = inner_population_val[j - 1]
        for k in range(0, 10):
          inner_population[i][k] = tempt[k]
        inner_population_val[i] = val
        break
    
    # random 
    ran = randint(11, 30)
    if (ran < 20):
      for k in range(0, 10):
        inner_population[ran][k] = tempt[k]
      inner_population_val[ran] = val
    
    
    obj_1.release()

  # cricial
  obj_3.acquire()
  if (count_thread == 19):
    obj_2.release()
  else:
    count_thread = count_thread + 1
  obj_3.release()

  return 0

def main_thread(s, data, list_constraint):
  global inner_population
  global inner_population_val
  global Random_population
  global count_thread

  count = 0

  while (True):
    count_thread = 0
    # Pick R
    for i in range(0, 20):
      if (count == 0):
        T = Thread(target=sub_thread, args=([], list_constraint, s, data,i, ))
      else:
        T = Thread(target=sub_thread, args=(inner_population[i], list_constraint, s, data,i, ))
      T.start()

    count = 1
    obj_2.acquire()
    print("t1: ", inner_population[0], " value: ", inner_population_val[0])
    print(inner_population_val)
    print()

    if (inner_population_val[0] == 0):
      return inner_population[0]

def intial_value():
  global inner_population 
  global inner_population_val 

  # intial inner_population
  for i in range(0, 20):
    tempt = []
    for j in range(0, 10):
      tempt.append("_")
    inner_population.append(tempt)
  
  # inital inner_population_val
  for i in range(0, 20):
    inner_population_val.append(-1)
  

if __name__ == "__main__":
  with open("input.txt","r") as input:
    data = input.readline()
    input.close()

  intial_value()
  s, data = handle_data(data)
  list_constraint = determine_constraint(data)

  result = main_thread(s, data, list_constraint)
  print(result)

  # sub_thread(['U', 'N', 'E', 'W', 'Y', 'P', 'O', 'B', 'R', 'L'], list_constraint, s, data)
  # print("__________________________________________________")
  # for i in range(0, 20):
  #   print("T: ", inner_population[i], " val: ", inner_population_val[i])
  # print(s)


