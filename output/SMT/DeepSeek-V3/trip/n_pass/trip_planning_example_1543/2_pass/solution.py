from z3 import *

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Cities and their required days
    cities = {
        "Prague": 3,
        "Warsaw": 4,
        "Dublin": 3,
        "Athens": 3,
        "Vilnius": 4,
        "Porto": 5,
        "London": 3,
        "Seville": 2,
        "Lisbon": 5,
        "Dubrovnik": 3
    }

    # Direct flights (undirected)
    direct_flights = [
        ("Warsaw", "Vilnius"),
        ("Prague", "Athens"),
        ("London", "Lisbon"),
        ("Lisbon", "Porto"),
        ("Prague", "Lisbon"),
        ("London", "Dublin"),
        ("Athens", "Vilnius"),
        ("Athens", "Dublin"),
        ("Prague", "London"),
        ("London", "Warsaw"),
        ("Dublin", "Seville"),
        ("Seville", "Porto"),
        ("Lisbon", "Athens"),
        ("Dublin", "Porto"),
        ("Athens", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Porto", "Warsaw"),
        ("Prague", "Warsaw"),
        ("Prague", "Dublin"),
        ("Athens", "Dubrovnik"),
        ("Lisbon", "Dublin"),
        ("Dubrovnik", "Dublin"),
        ("Lisbon", "Seville"),
        ("London", "Athens")
    ]

    # Create flight connections as a dictionary for easy lookup
    flight_connections = {}
    for city in cities:
        flight_connections[city] = []
    for a, b in direct_flights:
        flight_connections[a].append(b)
        flight_connections[b].append(a)

    # Variables for each city's start and end days
    city_start = {city: Int(f'start_{city}') for city in cities}
    city_end = {city: Int(f'end_{city}') for city in cities}

    # Constraints for start and end days
    for city in cities:
        s.add(city_start[city] >= 1)
        s.add(city_end[city] <= 26)
        s.add(city_end[city] >= city_start[city])
        s.add(city_end[city] - city_start[city] + 1 >= cities[city])

    # Fixed constraints
    # Prague: 3 days, between day 1-3 (workshop)
    s.add(city_start["Prague"] == 1)
    s.add(city_end["Prague"] == 3)

    # Warsaw: 4 days, meet friends between day 20-23
    s.add(city_start["Warsaw"] <= 20)
    s.add(city_end["Warsaw"] >= 23)
    s.add(city_end["Warsaw"] - city_start["Warsaw"] + 1 == 4)

    # Porto: 5 days, conference between day 16-20
    s.add(city_start["Porto"] <= 16)
    s.add(city_end["Porto"] >= 20)
    s.add(city_end["Porto"] - city_start["Porto"] + 1 == 5)

    # London: 3 days, wedding between day 3-5
    s.add(city_start["London"] <= 3)
    s.add(city_end["London"] >= 5)
    s.add(city_end["London"] - city_start["London"] + 1 == 3)

    # Lisbon: 5 days, relatives between day 5-9
    s.add(city_start["Lisbon"] <= 5)
    s.add(city_end["Lisbon"] >= 9)
    s.add(city_end["Lisbon"] - city_start["Lisbon"] + 1 == 5)

    # Other cities have flexible days but must meet their duration
    # Dublin: 3 days
    # Athens: 3 days
    # Vilnius: 4 days
    # Seville: 2 days
    # Dubrovnik: 3 days

    # Constraint: All city visits must be non-overlapping except for flight days
    for city1 in cities:
        for city2 in cities:
            if city1 == city2:
                continue
            s.add(Or(
                city_end[city1] < city_start[city2],
                city_end[city2] < city_start[city1],
                And(city_end[city1] == city_start[city2], city2 in flight_connections[city1]),
                And(city_end[city2] == city_start[city1], city1 in flight_connections[city2])
            ))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        # Extract the start and end days for each city
        city_days = {}
        for city in cities:
            start = model[city_start[city]].as_long()
            end = model[city_end[city]].as_long()
            city_days[city] = (start, end)

        # Now, build the itinerary
        itinerary = []
        current_stays = {}

        for day in range(1, 27):
            # Determine which cities are being visited on this day
            active_cities = [city for city in cities if city_days[city][0] <= day <= city_days[city][1]]
            # For each city, check if it's a new stay or continuing
            for city in active_cities:
                if city not in current_stays:
                    # New stay, starts on this day
                    current_stays[city] = day
            # Check for cities that are ending their stay on this day
            departing_cities = [city for city in current_stays if city_days[city][1] == day]
            for city in departing_cities:
                start_day = current_stays[city]
                if start_day == day:
                    itinerary.append({"day_range": f"Day {day}", "place": city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": city})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                del current_stays[city]
            # For cities that are continuing, no action needed
        # After loop, add any remaining stays
        for city in current_stays:
            start_day = current_stays[city]
            itinerary.append({"day_range": f"Day {start_day}-26", "place": city})

        # Now, handle flight days where two cities are present on the same day
        # Reconstruct the itinerary to include both cities on flight days
        final_itinerary = []
        i = 0
        while i < len(itinerary):
            current = itinerary[i]
            if i + 1 < len(itinerary) and itinerary[i+1]['day_range'] == current['day_range'] and itinerary[i+1]['place'] != current['place']:
                # Flight day, two cities on the same day
                final_itinerary.append({"day_range": current['day_range'], "place": current['place']})
                final_itinerary.append({"day_range": itinerary[i+1]['day_range'], "place": itinerary[i+1]['place']})
                i += 2
            else:
                final_itinerary.append(current)
                i += 1

        return {"itinerary": final_itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(result)