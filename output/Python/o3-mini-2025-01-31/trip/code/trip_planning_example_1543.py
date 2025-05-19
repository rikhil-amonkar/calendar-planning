import json

def plan_itinerary():
    # Define the fixed itinerary order with required durations.
    # Each tuple: (city, required duration in days)
    # The chosen order satisfies both direct flight connectivity and special event constraints.
    # Order:
    # 1. Prague: 3 days, workshop must occur between day1 and 3.
    # 2. London: 3 days, wedding must occur between day3 and 5.
    # 3. Lisbon: 5 days, visit relatives between day5 and 9.
    # 4. Athens: 3 days.
    # 5. Dubrovnik: 3 days.
    # 6. Dublin: 3 days.
    # 7. Seville: 2 days.
    # 8. Porto: 5 days, conference between day16 and 20.
    # 9. Warsaw: 4 days, meet friends between day20 and 23.
    # 10. Vilnius: 4 days.
    itinerary_plan = [
        ("Prague", 3),
        ("London", 3),
        ("Lisbon", 5),
        ("Athens", 3),
        ("Dubrovnik", 3),
        ("Dublin", 3),
        ("Seville", 2),
        ("Porto", 5),
        ("Warsaw", 4),
        ("Vilnius", 4)
    ]
    
    # For some cities there are fixed event date windows.
    # We will impose these by forcing the start of those segments.
    # Event constraints:
    #   - Prague: workshop must occur between day 1 and 3. (So Prague must include day 1-3)
    #   - London: wedding between day 3 and 5.
    #   - Lisbon: relatives visit between day 5 and 9.
    #   - Porto: conference between day 16 and 20.
    #   - Warsaw: friends meeting between day 20 and 23.
    
    # We will build the day ranges sequentially.
    # The rule: If flying from city A to B on day X, then day X is counted in both A and B.
    # Thus the start of the first city is day 1.
    # For each subsequent city, its start day is the end day of the previous city.
    # (This automatically makes the flight day overlap.)
    
    day = 1
    itinerary = []
    
    # Using our planned order, assign day ranges.
    # However, for Porto and Warsaw we have fixed requirements.
    fixed_starts = {
        "Prague": 1,         # Must start on day 1 (so workshop on days1-3)
        "London": None,      # Will be forced by previous end (ensuring wedding between 3-5)
        "Lisbon": None,      # Will follow from London so relatives are in Lisbon (days5-9)
        "Porto": 16,         # Must start on day 16 to allow conference on days16-20
        "Warsaw": 20         # Must start on day 20 to allow friends meeting on days20-23
    }
    
    for city, duration in itinerary_plan:
        # Check if city has a forced start day:
        if city in fixed_starts and fixed_starts[city] is not None:
            start_day = fixed_starts[city]
            day = start_day  # override current day with forced start day
        else:
            start_day = day
        
        # The end day is start_day + duration - 1.
        end_day = start_day + duration - 1
        
        # Add the itinerary segment as a dictionary with day_range and place.
        itinerary.append({
            "day_range": f"{start_day}-{end_day}",
            "place": city
        })
        
        # Set the next city's start day equal to the current segment's end day (flight overlap)
        day = end_day

    return itinerary

def main():
    itinerary = plan_itinerary()
    # Output the itinerary as JSON formatted dictionary (list of segments)
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()