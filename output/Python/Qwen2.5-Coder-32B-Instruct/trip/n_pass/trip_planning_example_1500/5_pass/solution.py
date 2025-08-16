import json

def calculate_itinerary():
    constraints = {
        "Zurich": (7, 8, None),       # Conference
        "Bucharest": (None, None, 2),  # Fixed duration
        "Hamburg": (None, None, 5),    # Fixed duration
        "Barcelona": (None, None, 4),  # Fixed duration
        "Reykjavik": (9, 13, 5),       # Visit relatives
        "Stuttgart": (None, None, 5),  # Fixed duration
        "Stockholm": (None, None, 2),  # Fixed duration
        "Tallinn": (None, None, 4),    # Fixed duration
        "Milan": (3, 7, 5),            # Meet friends
        "London": (1, 3, 3)            # Annual show
    }
    
    itinerary = []
    current_day = 1
    
    def add_to_itinerary(city, start_day, end_day):
        nonlocal current_day
        if start_day < current_day:
            start_day = current_day
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        current_day = end_day + 1
    
    # Handle fixed events first
    fixed_events = {
        "London": (1, 3),
        "Milan": (3, 7),
        "Zurich": (7, 8),
        "Reykjavik": (9, 13)
    }
    
    for city, (start_day, end_day) in fixed_events.items():
        add_to_itinerary(city, start_day, end_day)
    
    # Calculate remaining days
    remaining_days = 28 - (current_day - 1)
    
    # Cities with fixed durations
    cities_with_fixed_duration = {
        "Bucharest": 2,
        "Hamburg": 5,
        "Barcelona": 4,
        "Stuttgart": 5,
        "Stockholm": 2,
        "Tallinn": 4
    }
    
    # Assign remaining cities with fixed durations
    for city, days in cities_with_fixed_duration.items():
        if remaining_days >= days:
            add_to_itinerary(city, current_day, current_day + days - 1)
            remaining_days -= days
        else:
            break  # No more days to assign
    
    # If there are still remaining days, distribute them among the cities that haven't been fully assigned
    if remaining_days > 0:
        # Distribute remaining days to the last city if possible
        if itinerary and remaining_days <= (itinerary[-1]['day_range'].split('-')[1].split(' ')[1] - itinerary[-1]['day_range'].split('-')[0].split(' ')[1]):
            new_end_day = current_day + remaining_days - 1
            itinerary[-1]['day_range'] = f"Day {itinerary[-1]['day_range'].split('-')[0].split(' ')[1]}-{new_end_day}"
            current_day = new_end_day + 1
        else:
            # If not possible, create a new entry for the remaining days
            add_to_itinerary("Unassigned", current_day, current_day + remaining_days - 1)
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    print(json.dumps(calculate_itinerary(), indent=4))