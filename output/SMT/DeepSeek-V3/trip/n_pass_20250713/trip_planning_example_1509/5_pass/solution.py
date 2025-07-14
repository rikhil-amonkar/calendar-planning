import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Paris": 5,
        "Warsaw": 2,
        "Krakow": 2,
        "Tallinn": 2,
        "Riga": 2,
        "Copenhagen": 5,
        "Helsinki": 5,
        "Oslo": 5,
        "Santorini": 2,
        "Lyon": 4
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ("Warsaw", "Riga"),
        ("Warsaw", "Tallinn"),
        ("Copenhagen", "Helsinki"),
        ("Lyon", "Paris"),
        ("Copenhagen", "Warsaw"),
        ("Lyon", "Oslo"),
        ("Paris", "Oslo"),
        ("Paris", "Riga"),
        ("Krakow", "Helsinki"),
        ("Paris", "Tallinn"),
        ("Oslo", "Riga"),
        ("Krakow", "Warsaw"),
        ("Paris", "Helsinki"),
        ("Copenhagen", "Santorini"),
        ("Helsinki", "Warsaw"),
        ("Helsinki", "Riga"),
        ("Copenhagen", "Krakow"),
        ("Copenhagen", "Riga"),
        ("Paris", "Krakow"),
        ("Copenhagen", "Oslo"),
        ("Oslo", "Tallinn"),
        ("Oslo", "Helsinki"),
        ("Copenhagen", "Tallinn"),
        ("Oslo", "Krakow"),
        ("Riga", "Tallinn"),
        ("Helsinki", "Tallinn"),
        ("Paris", "Copenhagen"),
        ("Paris", "Warsaw"),
        ("Santorini", "Oslo"),
        ("Oslo", "Warsaw")
    ]
    
    # Create flight dictionary
    flight_dict = {}
    for a, b in direct_flights:
        if a not in flight_dict:
            flight_dict[a] = []
        if b not in flight_dict:
            flight_dict[b] = []
        flight_dict[a].append(b)
        flight_dict[b].append(a)
    
    # Fixed events
    fixed_events = {
        17: "Krakow",  # Workshop day 17-18
        23: "Riga",    # Wedding day 23-24
        12: "Santorini" # Relatives day 12-13
    }
    
    # Initialize itinerary
    itinerary = []
    current_city = None
    day = 1
    
    # Schedule fixed events first
    for event_day, city in sorted(fixed_events.items()):
        # Add days before event
        while day < event_day:
            # Choose a city that connects to next event
            possible_cities = [c for c in flight_dict.get(city, []) if cities[c] > 0]
            if possible_cities:
                next_city = possible_cities[0]
                stay_days = min(event_day - day, cities[next_city])
                itinerary.append({"day_range": f"Day {day}-{day+stay_days-1}", "place": next_city})
                cities[next_city] -= stay_days
                day += stay_days
                current_city = next_city
            else:
                # If no connecting city, stay in same city
                stay_days = event_day - day
                itinerary.append({"day_range": f"Day {day}-{day+stay_days-1}", "place": current_city})
                day += stay_days
        
        # Add event
        itinerary.append({"day_range": f"Day {event_day}-{event_day+1}", "place": city})
        cities[city] -= 2
        day = event_day + 2
        current_city = city
    
    # Add remaining days
    while day <= 25:
        # Choose a city with remaining days that connects to current city
        possible_cities = [c for c in flight_dict.get(current_city, []) if cities[c] > 0] if current_city else list(cities.keys())
        if possible_cities:
            next_city = possible_cities[0]
            stay_days = min(25 - day + 1, cities[next_city])
            itinerary.append({"day_range": f"Day {day}-{day+stay_days-1}", "place": next_city})
            cities[next_city] -= stay_days
            day += stay_days
            current_city = next_city
        else:
            # If no connecting city with remaining days, stay in same city
            stay_days = 25 - day + 1
            itinerary.append({"day_range": f"Day {day}-{day+stay_days-1}", "place": current_city})
            day += stay_days
    
    # Verify all city days are used
    for city, days in cities.items():
        if days != 0:
            return {"error": f"Could not allocate all days for {city}"}
    
    return {"itinerary": itinerary}

result = solve_itinerary()
print(json.dumps(result, indent=2))