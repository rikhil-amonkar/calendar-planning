import json

def plan_trip():
    # Define cities and their required days
    cities = {
        "Geneva": 6,
        "Split": 2,
        "Helsinki": 2,
        "Vilnius": 3,
        "Reykjavik": 3
    }
    
    # Direct flights between cities
    direct_flights = {
        "Split": ["Helsinki", "Geneva", "Vilnius"],
        "Helsinki": ["Split", "Geneva", "Reykjavik", "Vilnius"],
        "Geneva": ["Split", "Helsinki"],
        "Vilnius": ["Helsinki", "Split"],
        "Reykjavik": ["Helsinki"]
    }
    
    # Determine the order of cities
    # Based on the constraints, the order is: Geneva -> Split -> Vilnius -> Helsinki -> Reykjavik
    itinerary_order = ["Geneva", "Split", "Vilnius", "Helsinki", "Reykjavik"]
    
    # Calculate the day ranges for each city
    day_ranges = []
    current_day = 1
    
    for city in itinerary_order:
        days_in_city = cities[city]
        day_ranges.append((current_day, current_day + days_in_city - 1))
        current_day += days_in_city
    
    # Adjust day ranges to ensure Vilnius is 7-9 and Reykjavik is 10-12
    # This requires shifting the start of the cities after Vilnius
    # Calculate how much to shift
    vilnius_start = day_ranges[2][0]
    vilnius_end = day_ranges[2][1]
    shift_amount = 7 - vilnius_start
    
    # Adjust day ranges
    adjusted_ranges = []
    for start, end in day_ranges:
        adjusted_start = start + shift_amount
        adjusted_end = end + shift_amount
        adjusted_ranges.append((adjusted_start, adjusted_end))
    
    # Ensure Reykjavik is 10-12
    reykjavik_start = adjusted_ranges[4][0]
    reykjavik_shift = 10 - reykjavik_start
    for i in range(len(adjusted_ranges)):
        start, end = adjusted_ranges[i]
        adjusted_ranges[i] = (start + reykjavik_shift, end + reykjavik_shift)
    
    # Build the itinerary
    itinerary = []
    for i, city in enumerate(itinerary_order):
        start, end = adjusted_ranges[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    plan_trip()