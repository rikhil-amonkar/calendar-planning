from z3 import *

# Define the City enum type
City = Datatype('City')
City.declare('Split')
City.declare('Santorini')
City.declare('London')
City = City.create()
Split, Santorini, London = City.Split, City.Santorini, City.London

# Create variables for each day (1 to 18)
start = [ Const('start_%d' % i, City) for i in range(1,19) ]
fly = [ Bool('fly_%d' % i) for i in range(1,19) ]
dest = [ Const('dest_%d' % i, City) for i in range(1,19) ]

s = Solver()

# Constraints for days 1 to 17
for i in range(0, 17):  # i from 0 to 16 for days 1 to 17
    # If flying, ensure valid flight and set next day's start
    s.add(Implies(fly[i], 
                And(
                    Or(
                        And(start[i] == Split, dest[i] == London),
                        And(start[i] == Santorini, dest[i] == London),
                        And(start[i] == London, dest[i] == Split),
                        And(start[i] == London, dest[i] == Santorini)
                    ),
                    start[i+1] == dest[i]
                )))
    # If not flying, next day starts in the same city
    s.add(Implies(Not(fly[i]), start[i+1] == start[i]))

# Constraint for day 18 (no next day, but flight must be valid if flying)
i = 17  # day 18
s.add(Implies(fly[i],
            Or(
                And(start[i] == Split, dest[i] == London),
                And(start[i] == Santorini, dest[i] == London),
                And(start[i] == London, dest[i] == Split),
                And(start[i] == London, dest[i] == Santorini)
            )))

# Track days per city
inSplit = []
inSantorini = []
inLondon = []
for i in range(0,18):
    inSplit_i = If(fly[i], Or(start[i] == Split, dest[i] == Split), start[i] == Split)
    inSantorini_i = If(fly[i], Or(start[i] == Santorini, dest[i] == Santorini), start[i] == Santorini)
    inLondon_i = If(fly[i], Or(start[i] == London, dest[i] == London), start[i] == London)
    inSplit.append(inSplit_i)
    inSantorini.append(inSantorini_i)
    inLondon.append(inLondon_i)

total_Split = Sum([If(cond, 1, 0) for cond in inSplit])
total_Santorini = Sum([If(cond, 1, 0) for cond in inSantorini])
total_London = Sum([If(cond, 1, 0) for cond in inLondon])

s.add(total_Split == 6)
s.add(total_Santorini == 7)
s.add(total_London == 7)

# Conference constraints: in Santorini on day 12 and day 18
s.add(inSantorini[11] == True)  # day 12 is index 11
s.add(inSantorini[17] == True)  # day 18 is index 17

# Exactly 2 flight days
total_flights = Sum([If(fly[i], 1, 0) for i in range(0,18)])
s.add(total_flights == 2)

# Solve and output
if s.check() == sat:
    m = s.model()
    print("Day\tCities")
    for i in range(0,18):
        day = i+1
        start_val = m.evaluate(start[i])
        fly_val = m.evaluate(fly[i])
        if fly_val:
            dest_val = m.evaluate(dest[i])
            if start_val == dest_val:
                cities = str(start_val)
            else:
                cities = "{" + str(start_val) + ", " + str(dest_val) + "}"
            print(f"{day}\t{cities}")
        else:
            print(f"{day}\t{start_val}")
else:
    print("No solution found")