from z3 import *

# Define the City enum
City = Datatype('City')
City.declare('Split')
City.declare('Santorini')
City.declare('London')
City = City.create()
Split, Santorini, London = City.Split, City.Santorini, City.London

# Create variables for 18 days
start = [Const('start_%d' % i, City) for i in range(1, 19)]
fly = [Bool('fly_%d' % i) for i in range(1, 19)]
dest = [Const('dest_%d' % i, City) for i in range(1, 19)]

s = Solver()

# Flight validity constraints
for i in range(18):
    s.add(Implies(fly[i], 
                Or(
                    And(start[i] == London, dest[i] == Santorini),
                    And(start[i] == London, dest[i] == Split),
                    And(start[i] == Santorini, dest[i] == London),
                    And(start[i] == Split, dest[i] == London)
                )))

# Next day constraints for days 1-17
for i in range(17):
    s.add(Implies(fly[i], start[i+1] == dest[i]))
    s.add(Implies(Not(fly[i]), start[i+1] == start[i]))

# Track presence in each city per day
inSplit = []
inSantorini = []
inLondon = []
for i in range(18):
    inSplit_i = Or(And(Not(fly[i]), start[i] == Split),
                   And(fly[i], Or(start[i] == Split, dest[i] == Split)))
    inSantorini_i = Or(And(Not(fly[i]), start[i] == Santorini),
                       And(fly[i], Or(start[i] == Santorini, dest[i] == Santorini)))
    inLondon_i = Or(And(Not(fly[i]), start[i] == London),
                    And(fly[i], Or(start[i] == London, dest[i] == London)))
    inSplit.append(inSplit_i)
    inSantorini.append(inSantorini_i)
    inLondon.append(inLondon_i)

# Total days constraints
s.add(Sum([If(cond, 1, 0) for cond in inSplit]) == 6)
s.add(Sum([If(cond, 1, 0) for cond in inSantorini]) == 7)
s.add(Sum([If(cond, 1, 0) for cond in inLondon]) == 7)

# Conference constraints
s.add(inSantorini[11] == True)  # Day 12
s.add(inSantorini[17] == True)  # Day 18

# Flight count constraint
s.add(Sum([If(fly[i], 1, 0) for i in range(18)]) == 2)

# No flight on day 18
s.add(Not(fly[17]))

# Solve and print
if s.check() == sat:
    m = s.model()
    # Define city names for output
    city_names = {
        Split: "Split",
        Santorini: "Santorini",
        London: "London"
    }
    print("Day\tCities")
    for i in range(18):
        day = i + 1
        start_val = m.evaluate(start[i])
        fly_val = m.evaluate(fly[i])
        if fly_val:
            dest_val = m.evaluate(dest[i])
            # Get city names
            start_city = city_names[start_val]
            dest_city = city_names[dest_val]
            # Sort alphabetically for output
            cities_sorted = sorted([start_city, dest_city])
            cities = "{" + cities_sorted[0] + ", " + cities_sorted[1] + "}"
            print(f"{day}\t{cities}")
        else:
            print(f"{day}\t{city_names[start_val]}")
else:
    print("No solution found")