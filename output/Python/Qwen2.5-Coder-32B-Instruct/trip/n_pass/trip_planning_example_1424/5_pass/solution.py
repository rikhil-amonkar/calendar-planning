import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Warsaw": (3, None),
        "Porto": (5, (1, 5)),
        "Naples": (4, (17, 20)),
        "Brussels": (3, (20, 22)),
        "Split": (3, None),
        "Reykjavik": (5, None),
        "Amsterdam": (4, (5, 8)),
        "Lyon": (3, None),
        "Helsinki": (4, (8, 11)),
        "Valencia": (2, None)
    }
    
    # Define the direct flight connections
    flights = [
        ("Amsterdam", "Warsaw"), ("Helsinki", "Brussels"), ("Helsinki", "Warsaw"),
        ("Reykjavik", "Brussels"), ("Amsterdam", "Lyon"), ("Amsterdam", "Naples"),
        ("Amsterdam", "Reykjavik"), ("Naples", "Valencia"), ("Porto", "Brussels"),
        ("Amsterdam", "Split"), ("Lyon", "Split"), ("Warsaw", "Split"),
        ("Porto", "Amsterdam"), ("Helsinki", "Split"), ("Brussels", "Lyon"),
        ("Porto", "Lyon"), ("Reykjavik", "Warsaw"), ("Brussels", "Valencia"),
        ("Valencia", "Lyon"), ("Porto", "Warsaw"), ("Warsaw", "Valencia"),
        ("Amsterdam", "Helsinki"), ("Porto", "Valencia"), ("Warsaw", "Brussels"),
        ("Warsaw", "Naples"), ("Naples", "Split"), ("Helsinki", "Naples"),
        ("Helsinki", "Reykjavik"), ("Amsterdam", "Valencia"), ("Naples", "Brussels")
    ]
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Helper function to check if a flight is possible
    def can_fly(from_city, to_city):
        return (from_city, to_city) in flights or (to_city, from_city) in flights
    
    # Helper function to find the next city to fly to
    def find_next_city(current_city, current_day):
        for city, (days, event_days) in constraints.items():
            if city not in [entry["place"] for entry in itinerary]:  # Ensure we don't revisit cities
                if event_days is None or (current_day + days - 1 >= event_days[0] and current_day <= event_days[1]):
                    if can_fly(current_city, city):
                        return city
        return None
    
    # Start from a city with a specific start day requirement if possible
    start_city = "Porto"  # Starts on Day 1-5
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints[start_city][0] - 1}", "place": start_city})
    current_day += constraints[start_city][0]
    
    # Plan the rest of the itinerary
    while current_day < 28:
        next_city = find_next_city(itinerary[-1]["place"], current_day)
        if next_city:
            days_to_stay = constraints[next_city][0]
            if current_day + days_to_stay > 28:
                break
            itinerary.append({"day_range": f"Day {current_day}-{current_day + days_to_stay - 1}", "place": next_city})
            current_day += days_to_stay
        else:
            break
    
    # Ensure all constraints are met
    for city, (days, event_days) in constraints.items():
        if city not in [entry["place"] for entry in itinerary]:
            # Find a suitable place to insert the city
            for i, entry in enumerate(itinerary):
                start, end = map(int, entry["day_range"].split('-'))
                if event_days is not None and start >= event_days[0] and end <= event_days[1]:
                    if can_fly(itinerary[i-1]["place"], city):
                        itinerary.insert(i, {"day_range": f"Day {start - days}-{start - 1}", "place": city})
                        break
            else:
                # If no suitable place found, append at the end if possible
                if current_day + days <= 28:
                    itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})
                    current_day += days
    
    # Adjust the last entry to ensure it ends on Day 27
    if itinerary and int(itinerary[-1]["day_range"].split('-')[1]) > 27:
        last_start, last_end = map(int, itinerary[-1]["day_range"].split('-'))
        itinerary[-1]["day_range"] = f"Day {last_start}-27"
    
    return itinerary

# Calculate the itinerary and output it as JSON
itinerary = calculate_itinerary()
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))