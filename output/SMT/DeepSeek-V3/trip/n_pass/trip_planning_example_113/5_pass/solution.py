from z3 import *

def solve_itinerary():
    s = Solver()

    # City codes
    Milan, Naples, Seville = 0, 1, 2
    cities = {Milan: "Milan", Naples: "Naples", Seville: "Seville"}

    # Variables for each day's location (days 1 to 12)
    day_location = [Int(f"day_{i}") for i in range(1, 13)]

    # Each day must be one of the three cities
    for day in day_location:
        s.add(Or(day == Milan, day == Naples, day == Seville))

    # Flight constraints - only direct flights allowed
    # Milan <-> Seville and Milan <-> Naples
    for i in range(11):
        current = day_location[i]
        next_day = day_location[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            And(current == Milan, next_day == Seville),  # Milan -> Seville
            And(current == Seville, next_day == Milan),  # Seville -> Milan
            And(current == Naples, next_day == Milan),  # Naples -> Milan
            And(current == Milan, next_day == Naples)    # Milan -> Naples
        ))

    # Total days in each city
    milan_days = Sum([If(day == Milan, 1, 0) for day in day_location])
    naples_days = Sum([If(day == Naples, 1, 0) for day in day_location])
    seville_days = Sum([If(day == Seville, 1, 0) for day in day_location])

    s.add(milan_days == 7)
    s.add(naples_days == 3)
    s.add(seville_days == 4)

    # Days 9-12 must be in Seville (show days)
    for i in range(8, 12):  # days 9-12 (0-based index 8-11)
        s.add(day_location[i] == Seville)

    # Must visit Naples before the Seville show
    # At least one day in Naples before day 9
    s.add(Or([day_location[i] == Naples for i in range(8)]))

    # Additional constraints to help guide the solver
    # Start in Milan (arbitrary choice to reduce search space)
    s.add(day_location[0] == Milan)
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(12):
            day_num = i + 1
            city_code = model.evaluate(day_location[i]).as_long()
            city_name = cities[city_code]
            itinerary.append({"day": day_num, "place": city_name})
        
        # Verify the solution meets all requirements
        milan_count = sum(1 for day in itinerary if day["place"] == "Milan")
        naples_count = sum(1 for day in itinerary if day["place"] == "Naples")
        seville_count = sum(1 for day in itinerary if day["place"] == "Seville")
        show_days = all(day["place"] == "Seville" for day in itinerary[8:12])
        
        if (milan_count == 7 and naples_count == 3 and 
            seville_count == 4 and show_days):
            return {"itinerary": itinerary}
        else:
            return {"error": "Found invalid solution"}
    else:
        return {"error": "No valid itinerary found"}

# Generate and print the itinerary
itinerary = solve_itinerary()
print(itinerary)