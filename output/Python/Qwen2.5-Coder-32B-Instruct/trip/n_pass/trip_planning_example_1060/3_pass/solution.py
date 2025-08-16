import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Stuttgart": {"days": 4, "must_days": [4, 7]},
        "Istanbul": {"days": 4, "must_days": [19, 20, 21, 22]},
        "Vilnius": {"days": 4},
        "Seville": {"days": 3},
        "Geneva": {"days": 5},
        "Valencia": {"days": 5},
        "Munich": {"days": 3, "must_days": [13, 14, 15]},
        "Reykjavik": {"days": 4, "must_days": [1, 2, 3, 4]}
    }

    # Define the direct flights
    flights = [
        ("Geneva", "Istanbul"), ("Reykjavik", "Munich"), ("Stuttgart", "Valencia"),
        ("Reykjavik", "Stuttgart"), ("Stuttgart", "Istanbul"), ("Munich", "Geneva"),
        ("Istanbul", "Vilnius"), ("Valencia", "Seville"), ("Valencia", "Istanbul"),
        ("Vilnius", "Munich"), ("Seville", "Munich"), ("Munich", "Istanbul"),
        ("Valencia", "Geneva"), ("Valencia", "Munich")
    ]

    # Initialize the itinerary
    itinerary = []
    current_day = 1
    available_cities = set(constraints.keys())
    
    # Function to check if a city can be visited on given start day
    def can_visit(city, start_day):
        city_constraints = constraints[city]
        if "must_days" in city_constraints:
            for day in city_constraints["must_days"]:
                if day < start_day or day >= start_day + city_constraints["days"]:
                    return False
        return True
    
    # Function to find the next city to visit
    def find_next_city(current_city, current_day):
        for city in available_cities:
            if city != current_city and (current_city, city) in flights and can_visit(city, current_day):
                return city
        return None
    
    # Ensure Reykjavik is visited first due to its must_days constraint
    next_city = "Reykjavik"
    while current_day <= 25:
        if next_city:
            city_constraints = constraints[next_city]
            days_to_stay = city_constraints["days"]
            if current_day + days_to_stay - 1 > 25:
                break  # Cannot stay longer than 25 days
            itinerary.append({"day_range": f"Day {current_day}-{current_day + days_to_stay - 1}", "place": next_city})
            current_day += days_to_stay
            available_cities.remove(next_city)
            
            # Find the next city to visit
            last_city = next_city
            next_city = find_next_city(last_city, current_day)
            
            # If no next city found, try to find a city that fits the remaining days
            if not next_city and current_day <= 25:
                for city in available_cities:
                    if can_visit(city, current_day):
                        next_city = city
                        break
        else:
            break
    
    # Ensure the itinerary covers exactly 25 days
    if current_day < 25:
        # Add a placeholder or revisit a city if necessary
        last_city = itinerary[-1]["place"]
        city_constraints = constraints[last_city]
        days_to_stay = min(25 - current_day + 1, city_constraints["days"])
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days_to_stay - 1}", "place": last_city})
    
    # Adjust the itinerary to respect must_days
    adjusted_itinerary = []
    current_day = 1
    available_cities = set(constraints.keys())
    for entry in itinerary:
        city = entry["place"]
        city_constraints = constraints[city]
        days_to_stay = city_constraints["days"]
        if "must_days" in city_constraints:
            must_days = city_constraints["must_days"]
            start_day = must_days[0] - 1  # Convert to 0-based index
            days_to_stay = len(must_days)
            adjusted_itinerary.append({"day_range": f"Day {start_day + 1}-{start_day + days_to_stay}", "place": city})
            current_day = start_day + days_to_stay + 1
            available_cities.remove(city)
        else:
            adjusted_itinerary.append(entry)
            current_day += days_to_stay
            available_cities.remove(city)
    
    # Ensure the itinerary covers exactly 25 days
    if current_day < 25:
        # Add a placeholder or revisit a city if necessary
        last_city = adjusted_itinerary[-1]["place"]
        city_constraints = constraints[last_city]
        days_to_stay = min(25 - current_day + 1, city_constraints["days"])
        adjusted_itinerary.append({"day_range": f"Day {current_day}-{current_day + days_to_stay - 1}", "place": last_city})
    
    return {"itinerary": adjusted_itinerary}

# Calculate and print the itinerary as JSON
print(json.dumps(calculate_itinerary(), indent=4))