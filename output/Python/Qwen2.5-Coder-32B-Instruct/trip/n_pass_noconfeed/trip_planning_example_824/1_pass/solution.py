import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Berlin": (1, 5),  # Annual show
        "Split": (None, 3),
        "Bucharest": (13, 3),  # Visit relatives
        "Riga": (None, 5),
        "Lisbon": (None, 3),
        "Tallinn": (None, 4),
        "Lyon": (7, 5)  # Attend wedding
    }
    
    # Define the direct flight connections
    flights = [
        ("Lisbon", "Bucharest"),
        ("Berlin", "Lisbon"),
        ("Bucharest", "Riga"),
        ("Berlin", "Riga"),
        ("Split", "Lyon"),
        ("Lisbon", "Riga"),
        ("Riga", "Tallinn"),
        ("Berlin", "Split"),
        ("Lyon", "Lisbon"),
        ("Berlin", "Tallinn"),
        ("Lyon", "Bucharest")
    ]
    
    # Initialize the itinerary
    itinerary = []
    
    # Add fixed events first
    for city, (start, duration) in constraints.items():
        if start is not None:
            end = start + duration - 1
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
    
    # Sort itinerary by start day
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))
    
    # Fill in the gaps with the remaining cities
    current_day = 1
    cities_to_visit = ["Berlin", "Split", "Bucharest", "Riga", "Lisbon", "Tallinn", "Lyon"]
    
    for entry in itinerary:
        start_day = int(entry["day_range"].split()[1].split('-')[0])
        if start_day > current_day:
            # Find a city to visit in the gap
            for city in cities_to_visit:
                if constraints[city][0] is None:
                    # Check if we can fly to this city from the last visited city
                    last_city = itinerary[-1]["place"] if itinerary else None
                    if last_city is None or (last_city, city) in flights or (city, last_city) in flights:
                        constraints[city] = (current_day, constraints[city][1])
                        end_day = current_day + constraints[city][1] - 1
                        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
                        current_day = end_day + 1
                        break
    
    # Sort the final itinerary by day
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())