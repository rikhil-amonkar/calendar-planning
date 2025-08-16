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
    for place, (start, duration) in constraints.items():
        if start is not None:
            end = start + duration - 1
            itinerary.append({"day_range": f"Day {start}-{end}", "place": place})
    
    # Sort the itinerary by start day
    itinerary.sort(key=lambda x: int(x["day_range"].split('-')[0].split(' ')[-1]))
    
    # Create a set of all days covered by fixed events
    covered_days = set()
    for entry in itinerary:
        start, end = map(int, entry["day_range"].split('-')[0].split(' ')[-1]), map(int, entry["day_range"].split('-')[1].split(' ')[-1])
        covered_days.update(range(start, end + 1))
    
    # Find remaining days that need to be filled
    remaining_days = set(range(1, 23)) - covered_days
    
    # Function to find the next possible city
    def find_next_city(current_city, current_day):
        for city in ["Split", "Riga", "Lisbon", "Tallinn"]:
            if constraints[city][0] is None and city not in [entry["place"] for entry in itinerary]:
                for flight in flights:
                    if (flight[0] == current_city and flight[1] == city) or (flight[1] == current_city and flight[0] == city):
                        return city
        return None
    
    # Fill in the remaining days
    current_city = "Berlin"
    current_day = 1
    
    while remaining_days:
        if current_day not in remaining_days:
            current_day += 1
            continue
        
        next_city = find_next_city(current_city, current_day)
        if next_city:
            days_to_stay = constraints[next_city][1] if constraints[next_city][1] else 3  # Default to 3 days if not specified
            start_day = current_day
            end_day = min(start_day + days_to_stay - 1, max(remaining_days))
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": next_city})
            remaining_days -= set(range(start_day, end_day + 1))
            current_city = next_city
            current_day = end_day + 1
        else:
            break
    
    # If there are still remaining days, add them to the last city visited or any other city
    if remaining_days:
        last_entry = itinerary[-1]
        last_city = last_entry["place"]
        last_end_day = int(last_entry["day_range"].split('-')[1].split(' ')[-1])
        additional_days = len(remaining_days)
        new_end_day = last_end_day + additional_days
        itinerary[-1]["day_range"] = f"Day {last_end_day + 1}-{new_end_day}"
    
    # Ensure the itinerary covers exactly 22 days
    if int(itinerary[-1]["day_range"].split('-')[1].split(' ')[-1]) < 22:
        last_entry = itinerary[-1]
        last_city = last_entry["place"]
        last_start_day = int(last_entry["day_range"].split('-')[0].split(' ')[-1])
        new_end_day = 22
        itinerary[-1]["day_range"] = f"Day {last_start_day}-{new_end_day}"
    
    # Sort the itinerary by day range
    itinerary.sort(key=lambda x: int(x["day_range"].split('-')[0].split(' ')[-1]))
    
    return {"itinerary": itinerary}

# Output the result as JSON
print(json.dumps(calculate_itinerary(), indent=4))