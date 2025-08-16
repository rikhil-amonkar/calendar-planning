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

    def can_visit(city, start_day):
        city_constraints = constraints[city]
        if "must_days" in city_constraints:
            for day in city_constraints["must_days"]:
                if day < start_day or day >= start_day + city_constraints["days"]:
                    return False
        return True

    def find_next_city(current_city, current_day):
        for city in available_cities:
            if city != current_city and (current_city, city) in flights and can_visit(city, current_day):
                return city
        return None

    while current_day <= 25:
        if not itinerary:
            # Start with Reykjavik due to must_days constraint
            next_city = "Reykjavik"
        else:
            last_city = itinerary[-1]["place"]
            next_city = find_next_city(last_city, current_day)
        
        if next_city:
            city_constraints = constraints[next_city]
            days_to_stay = city_constraints["days"]
            itinerary.append({"day_range": f"Day {current_day}-{current_day + days_to_stay - 1}", "place": next_city})
            current_day += days_to_stay
            available_cities.remove(next_city)
        else:
            break

    return {"itinerary": itinerary}

# Calculate and print the itinerary as JSON
print(json.dumps(calculate_itinerary(), indent=4))