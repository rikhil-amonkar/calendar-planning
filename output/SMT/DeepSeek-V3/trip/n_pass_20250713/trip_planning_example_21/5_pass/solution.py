from z3 import *

def solve_itinerary():
    s = Solver()

    # Cities encoding
    Mykonos = 1
    Vienna = 2
    Venice = 3

    # Variables for each day
    days = [Int(f"day_{i}") for i in range(1, 11)]

    # Each day must be one of the cities
    for day in days:
        s.add(Or(day == Mykonos, day == Vienna, day == Venice))

    # Flight connections constraints
    for i in range(9):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            And(current == Mykonos, next_day == Vienna),
            And(current == Vienna, next_day == Mykonos),
            And(current == Vienna, next_day == Venice),
            And(current == Venice, next_day == Vienna)
        ))

    # Total days in each city
    s.add(Sum([If(day == Venice, 1, 0) for day in days]) == 6)
    s.add(Sum([If(day == Mykonos, 1, 0) for day in days]) == 2)
    s.add(Sum([If(day == Vienna, 1, 0) for day in days]) == 4)

    # Workshop constraint: at least one Venice day between 5-10
    s.add(Or([days[i] == Venice for i in range(4, 10)]))

    # Additional constraint: Venice must be visited consecutively for the workshop
    # This helps ensure the workshop is properly scheduled
    for i in range(4, 9):
        s.add(Implies(days[i] == Venice, Or(days[i-1] == Venice, days[i+1] == Venice)))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        
        for i in range(10):
            day_num = i + 1
            place_num = model.evaluate(days[i]).as_long()
            place = {1: "Mykonos", 2: "Vienna", 3: "Venice"}[place_num]
            
            if i == 0:
                current_place = place
                start_day = 1
            else:
                if place != current_place:
                    itinerary.append({
                        "day_range": f"Day {start_day}-{i}",
                        "place": current_place
                    })
                    itinerary.append({
                        "day_range": f"Day {i}",
                        "place": current_place
                    })
                    itinerary.append({
                        "day_range": f"Day {i}",
                        "place": place
                    })
                    current_place = place
                    start_day = i + 1
        
        itinerary.append({
            "day_range": f"Day {start_day}-10",
            "place": current_place
        })

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))