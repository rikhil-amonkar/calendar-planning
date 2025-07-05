from z3 import *

def solve_scheduling_problem():
    cities = ["Seville", "Stuttgart", "Porto", "Madrid"]
    direct_flights = {
        "Porto": ["Stuttgart", "Seville", "Madrid"],
        "Seville": ["Porto", "Madrid"],
        "Madrid": ["Porto", "Seville"],
        "Stuttgart": ["Porto"]
    }
    
    s = Solver()
    day_city = [Int(f"day_{i}_city") for i in range(1, 14)]
    
    for day in day_city:
        s.add(day >= 0, day < 4)
    
    # Must be in Madrid days 1-4
    for i in range(4):
        s.add(day_city[i] == 3)  # Madrid is index 3
    
    # Must be in Stuttgart days 7 and 13
    s.add(day_city[6] == 1)  # day 7
    s.add(day_city[12] == 1)  # day 13
    
    # Total days in each city
    s.add(Sum([If(day == 0, 1, 0) for day in day_city]) == 2)  # Seville
    s.add(Sum([If(day == 1, 1, 0) for day in day_city]) == 7)   # Stuttgart
    s.add(Sum([If(day == 2, 1, 0) for day in day_city]) == 3)   # Porto
    s.add(Sum([If(day == 3, 1, 0) for day in day_city]) == 4)   # Madrid
    
    # Flight transitions
    for i in range(12):
        current = day_city[i]
        next_ = day_city[i+1]
        s.add(Or(
            current == next_,
            And(current != next_,
                Or([And(current == cities.index(c), next_ == cities.index(n))
                    for c in direct_flights 
                    for n in direct_flights[c]
                ])
            )
        ))
    
    if s.check() == sat:
        model = s.model()
        schedule = [model.evaluate(day).as_long() for day in day_city]
        city_sequence = [cities[idx] for idx in schedule]
        
        itinerary = []
        current_city = city_sequence[0]
        start_day = 1
        
        for day in range(1, 13):
            if city_sequence[day] != current_city:
                if start_day == day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": city_sequence[day]})
                current_city = city_sequence[day]
                start_day = day + 1
        
        if start_day <= 13:
            if start_day == 13:
                itinerary.append({"day_range": f"Day 13", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-13", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_scheduling_problem()
print(result)