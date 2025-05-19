import json

def compute_itinerary():
    # Input constraints
    total_days = 16

    # Cities and their required days (including overlapping flight days except for the first city)
    # Order: Mykonos, London, Copenhagen, Tallinn, Oslo, Nice
    # Flight connectivity order: Mykonos->London, London->Copenhagen, Copenhagen->Tallinn, Tallinn->Oslo, Oslo->Nice.
    # Special requirements:
    # - Mykonos: 4 days
    # - London: 2 days
    # - Copenhagen: 3 days
    # - Tallinn: 4 days
    # - Oslo: 5 days (with friend meeting between day 10 and 14, ensured by schedule below)
    # - Nice: 3 days (and must be in Nice on day 14 and day 16 for conference)
    city_requirements = [
        ("Mykonos", 4),
        ("London", 2),
        ("Copenhagen", 3),
        ("Tallinn", 4),
        ("Oslo", 5),
        ("Nice", 3)
    ]

    itinerary = []
    current_day = 1
    
    # For the first city, use the full required days.
    for index, (city, req_days) in enumerate(city_requirements):
        if index == 0:
            start_day = current_day
            end_day = start_day + req_days - 1
            current_day = end_day  # flight will happen on the last day (overlap)
        else:
            # The flight day is the same as the previous segment's last day,
            # so for subsequent cities, count that day as already in the new city.
            start_day = current_day  # overlapping flight day from previous city
            # Add the remaining days (req_days - 1) to satisfy the total required days.
            end_day = start_day + (req_days - 1)
            current_day = end_day
        
        itinerary.append({
            "day_range": f"{start_day}-{end_day}",
            "place": city
        })
    
    # Check overall day count: last day's should match total_days
    if current_day != total_days:
        # If not, adjust the final itinerary's end day (should not happen with the given numbers)
        itinerary[-1]["day_range"] = f"{itinerary[-1]['day_range'].split('-')[0]}-{total_days}"
    
    return itinerary

if __name__ == "__main__":
    plan = compute_itinerary()
    # Output as JSON-formatted data
    print(json.dumps(plan, indent=2))