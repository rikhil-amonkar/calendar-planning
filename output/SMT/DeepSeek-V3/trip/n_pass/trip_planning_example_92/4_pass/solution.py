from z3 import *

def solve_trip_plan():
    s = Solver()

    days = 12
    City = Datatype('City')
    City.declare('Dublin')
    City.declare('Riga')
    City.declare('Vilnius')
    City = City.create()

    # Variables for each day's city
    day_city = [Const(f'day_{i}_city', City) for i in range(days)]

    # Direct flights: Dublin <-> Riga, Riga <-> Vilnius
    # No direct flights between Dublin and Vilnius
    
    # Transition constraints
    for i in range(days - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        s.add(Or(
            current == next_day,  # Stay in same city
            And(current == City.Dublin, next_day == City.Riga),
            And(current == City.Riga, next_day == City.Dublin),
            And(current == City.Riga, next_day == City.Vilnius),
            And(current == City.Vilnius, next_day == City.Riga)
        ))

    # Total days constraints (including flight days)
    total_riga = sum([If(day_city[i] == City.Riga, 1, 0) for i in range(days)])
    total_vilnius = sum([If(day_city[i] == City.Vilnius, 1, 0) for i in range(days)])
    total_dublin = sum([If(day_city[i] == City.Dublin, 1, 0) for i in range(days)])

    s.add(total_riga == 5)
    s.add(total_vilnius == 7)
    s.add(total_dublin == 2)

    # Try starting in each city to find a valid sequence
    for start_city in [City.Dublin, City.Riga, City.Vilnius]:
        s.push()
        s.add(day_city[0] == start_city)
        
        if s.check() == sat:
            m = s.model()
            itinerary = []
            for i in range(days):
                city_val = m.eval(day_city[i])
                city = "Dublin" if city_val == City.Dublin else \
                       "Riga" if city_val == City.Riga else \
                       "Vilnius"
                itinerary.append({"day": i+1, "city": city})
            
            # Verify totals
            riga_days = sum(1 for entry in itinerary if entry["city"] == "Riga")
            vilnius_days = sum(1 for entry in itinerary if entry["city"] == "Vilnius")
            dublin_days = sum(1 for entry in itinerary if entry["city"] == "Dublin")
            
            if riga_days == 5 and vilnius_days == 7 and dublin_days == 2:
                # Verify transitions
                valid = True
                for i in range(len(itinerary) - 1):
                    current = itinerary[i]["city"]
                    next_city = itinerary[i+1]["city"]
                    if current != next_city:
                        if not ((current == "Dublin" and next_city == "Riga") or
                               (current == "Riga" and next_city == "Dublin") or
                               (current == "Riga" and next_city == "Vilnius") or
                               (current == "Vilnius" and next_city == "Riga")):
                            valid = False
                            break
                if valid:
                    return {"itinerary": itinerary}
        s.pop()

    return {"error": "No valid itinerary found"}

result = solve_trip_plan()
import json
print(json.dumps(result, indent=2))