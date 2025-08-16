import json

def calculate_itinerary():
    constraints = {
        "Zurich": (7, 8, None),
        "Bucharest": (None, None, 2),
        "Hamburg": (None, None, 5),
        "Barcelona": (None, None, 4),
        "Reykjavik": (9, 13, 5),
        "Stuttgart": (None, None, 5),
        "Stockholm": (None, None, 2),
        "Tallinn": (None, None, 4),
        "Milan": (3, 7, 5),
        "London": (1, 3, 3)
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
    add_to_itinerary("London", 1, 3)  # Annual show
    add_to_itinerary("Milan", 3, 7)   # Meet friends
    add_to_itinerary("Zurich", 7, 8)  # Conference
    add_to_itinerary("Reykjavik", 9, 13)  # Visit relatives
    
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
    
    # If there are still remaining days, distribute them among the cities that haven't been fully assigned
    if remaining_days > 0:
        # Add any remaining days to the last city or distribute them evenly
        # Here we will just add them to the last city for simplicity
        last_city = itinerary[-1]['place']
        new_end_day = current_day + remaining_days - 1
        itinerary[-1]['day_range'] = f"Day {itinerary[-1]['day_range'].split('-')[0].split(' ')[1]}-{new_end_day}"
        current_day = new_end_day + 1
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    print(json.dumps(calculate_itinerary(), indent=4))