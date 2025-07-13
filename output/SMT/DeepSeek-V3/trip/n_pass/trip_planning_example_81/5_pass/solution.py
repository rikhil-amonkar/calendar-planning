from z3 import *

def solve_itinerary():
    s = Solver()

    # Define cities
    Mykonos, Budapest, Hamburg = 1, 2, 3
    city_names = {Mykonos: "Mykonos", Budapest: "Budapest", Hamburg: "Hamburg"}

    # Variables for each day's city
    days = 9
    day_city = [Int(f"day_{i}") for i in range(1, days+1)]

    # Each day must be one of the cities
    for i in range(days):
        s.add(Or([day_city[i] == city for city in [Mykonos, Budapest, Hamburg]]))

    # Required days in Mykonos
    s.add(day_city[3] == Mykonos)  # Day 4
    s.add(day_city[8] == Mykonos)   # Day 9

    # Count days in each city
    mykonos_days = Sum([If(day_city[i] == Mykonos, 1, 0) for i in range(days)])
    budapest_days = Sum([If(day_city[i] == Budapest, 1, 0) for i in range(days)])
    hamburg_days = Sum([If(day_city[i] == Hamburg, 1, 0) for i in range(days)])

    s.add(mykonos_days == 6)
    s.add(budapest_days == 3)
    s.add(hamburg_days == 2)

    # Flight constraints - only direct flights allowed
    for i in range(days-1):
        current = day_city[i]
        next_ = day_city[i+1]
        s.add(Or(
            current == next_,  # Stay in same city
            And(current == Budapest, next_ == Mykonos),
            And(current == Mykonos, next_ == Budapest),
            And(current == Hamburg, next_ == Budapest),
            And(current == Budapest, next_ == Hamburg)
        ))

    # Check for solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Track stays and flights
        stays = []
        for day in range(1, days+1):
            city = model.evaluate(day_city[day-1]).as_long()
            stays.append(city_names[city])
        
        # Build itinerary with flight days
        current_stay = stays[0]
        start_day = 1
        
        for day in range(2, days+1):
            if stays[day-1] != stays[day-2]:
                # Add previous stay
                if start_day == day-1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": stays[day-2]})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": stays[day-2]})
                
                # Add flight day (counts for both cities)
                itinerary.append({"day_range": f"Day {day}", "place": stays[day-2]})
                itinerary.append({"day_range": f"Day {day}", "place": stays[day-1]})
                start_day = day+1
        
        # Add final stay
        if start_day <= days:
            if start_day == days:
                itinerary.append({"day_range": f"Day {start_day}", "place": stays[-1]})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{days}", "place": stays[-1]})

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print
result = solve_itinerary()
print(result)