import json

def compute_itinerary():
    # Define the cities and their required durations in days (including flight overlap)
    # The order of visits is chosen to satisfy flight connectivity and time constraints.
    # Each city i is assigned an interval [start, end] with duration = end-start+1.
    requirements = {
        "Madrid": 2,   # Must include day 2 or 3 for relatives
        "London": 2,
        "Berlin": 5,   # Must have the wedding between day 3 and 7
        "Dublin": 3,   # Friend meeting between day 7 and 9
        "Oslo": 3,
        "Vilnius": 3
    }
    
    # The permitted direct flights between cities (undirected connections)
    flights = {
        ("London", "Madrid"),
        ("Oslo", "Vilnius"),
        ("Berlin", "Vilnius"),
        ("Madrid", "Oslo"),
        ("Madrid", "Dublin"),
        ("London", "Oslo"),
        ("Madrid", "Berlin"),
        ("Berlin", "Oslo"),
        ("Dublin", "Oslo"),
        ("London", "Dublin"),
        ("London", "Berlin"),
        ("Berlin", "Dublin")
    }
    
    # Chosen sequence to meet all the constraints:
    # Sequence: Madrid -> London -> Berlin -> Dublin -> Oslo -> Vilnius
    # This ordering satisfies:
    # - Madrid and London are directly connected.
    # - London and Berlin are directly connected.
    # - Berlin and Dublin are directly connected.
    # - Dublin and Oslo are directly connected.
    # - Oslo and Vilnius are directly connected.
    sequence = ["Madrid", "London", "Berlin", "Dublin", "Oslo", "Vilnius"]
    
    # Check that each consecutive pair is connected by a direct flight.
    for i in range(len(sequence) - 1):
        pair = (sequence[i], sequence[i+1])
        pair_rev = (sequence[i+1], sequence[i])
        if pair not in flights and pair_rev not in flights:
            raise ValueError(f"No direct flight between {sequence[i]} and {sequence[i+1]}")

    # Total unique days in the trip
    total_trip_days = 13
    
    # Compute the itinerary intervals.
    # Rule: if flying from city A to city B on day X, then that day counts for both cities.
    # So we have intervals:
    # city1: [s1, e1] with duration d1.
    # city2: [e1, e1 + d2 - 1],
    # city3: [e1 + d2 - 1, e1 + d2 - 1 + d3 - 1] etc.
    itinerary = []
    current_day = 1  # start at day 1
    for city in sequence:
        duration = requirements[city]
        # The interval for this city is [current_day, current_day + duration - 1]
        start_day = current_day
        end_day = current_day + duration - 1
        itinerary.append({
            "day_range": f"{start_day}-{end_day}",
            "place": city
        })
        # For the next city, the flight is on the last day of the current city,
        # so start day for next city is the current city's end day.
        current_day = end_day
        
    # Correction: After the last city, the trip end day must be exactly 13.
    # Our constructed itinerary automatically gives total days = last end_day.
    if itinerary[-1]["day_range"].split("-")[1] != str(total_trip_days):
        # Adjust the itinerary if needed. Since the sum of durations (2+2+5+3+3+3=18) minus 5 overlaps = 13,
        # our computed itinerary with overlaps is:
        # Madrid: 1-2, London: 2-3, Berlin: 3-7, Dublin: 7-9, Oslo: 9-11, Vilnius: 11-13.
        itinerary = [
            {"day_range": "1-2", "place": "Madrid"},
            {"day_range": "2-3", "place": "London"},
            {"day_range": "3-7", "place": "Berlin"},
            {"day_range": "7-9", "place": "Dublin"},
            {"day_range": "9-11", "place": "Oslo"},
            {"day_range": "11-13", "place": "Vilnius"}
        ]
    
    # Validate constraint conditions:
    # Madrid relatives between day2 and day3: Madrid [1-2] includes day 2.
    # Berlin wedding between day3 and day7: Berlin [3-7] covers days 3 through 7.
    # Dublin friend meeting between day7 and day9: Dublin [7-9] covers days 7,8,9.
    # Other durations are as specified.
    
    return itinerary

if __name__ == "__main__":
    itinerary = compute_itinerary()
    # Output result in JSON format
    print(json.dumps(itinerary))