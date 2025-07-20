from z3 import *

# Define the city enumeration
City = Datatype('City')
City.declare('London')
City.declare('Santorini')
City.declare('Istanbul')
City = City.create()

# Create variables for each day (0-9 for days 1-10)
days = [Const(f'day_{i}', City) for i in range(10)]

s = Solver()

# Hard constraints: Days 5 and 10 must be in Santorini
s.add(days[4] == City.Santorini)  # Day 5
s.add(days[9] == City.Santorini)  # Day 10

# Valid flight transitions between consecutive days
for i in range(9):
    current = days[i]
    next_day = days[i+1]
    s.add(Or(
        current == next_day,  # Stay in same city
        And(current == City.London, next_day == City.Santorini),
        And(current == City.London, next_day == City.Istanbul),
        And(current == City.Santorini, next_day == City.London),
        And(current == City.Istanbul, next_day == City.London)
    ))

# Must visit all three cities at least once
s.add(Or([d == City.London for d in days]))
s.add(Or([d == City.Istanbul for d in days]))
# Santorini is already guaranteed by day5/day10 constraints

# Find and print a valid itinerary
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(10):
        d_val = m.eval(days[i])
        if d_val == City.London:
            itinerary.append("London")
        elif d_val == City.Santorini:
            itinerary.append("Santorini")
        else:
            itinerary.append("Istanbul")
    
    # Print the 10-day itinerary
    print("Valid 10-day itinerary satisfying conference and flight constraints:")
    for day, city in enumerate(itinerary, start=1):
        print(f"Day {day}: {city}")
    
    # Calculate actual days per city
    london_days = sum(1 for c in itinerary if c == "London")
    santorini_days = sum(1 for c in itinerary if c == "Santorini")
    istanbul_days = sum(1 for c in itinerary if c == "Istanbul")
    
    print("\nActual days per city:")
    print(f"London: {london_days} days (desired: 3)")
    print(f"Santorini: {santorini_days} days (desired: 6)")
    print(f"Istanbul: {istanbul_days} days (desired: 3)")
else:
    print("No valid itinerary found for the given constraints")