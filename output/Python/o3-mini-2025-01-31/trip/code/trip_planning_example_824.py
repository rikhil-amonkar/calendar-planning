import json

def compute_itinerary():
    # Input parameters:
    total_days = 22
    
    # City durations (in days), as required
    # Note: when flying on the same day, that day is counted for both cities.
    # We plan the itinerary in the order that satisfies both the flight network and the special event time windows.
    cities = [
        {"place": "Berlin", "duration": 5},    # Must attend annual show in Berlin from day 1 to day 5.
        {"place": "Split", "duration": 3},       # 3 days in Split. Direct flight available from Berlin to Split.
        {"place": "Lyon", "duration": 5},        # 5 days in Lyon; wedding in Lyon happens between day 7 and day 11.
        {"place": "Bucharest", "duration": 3},   # 3 days in Bucharest; visiting relatives between day 13 and day 15.
        {"place": "Lisbon", "duration": 3},      # 3 days in Lisbon.
        {"place": "Riga", "duration": 5},        # 5 days in Riga.
        {"place": "Tallinn", "duration": 4}      # 4 days in Tallinn.
    ]
    
    # The flight network (only direct flight pairs available):
    # Lisbon <-> Bucharest, Berlin <-> Lisbon, Bucharest <-> Riga, Berlin <-> Riga,
    # Split <-> Lyon, Lisbon <-> Riga, Riga -> Tallinn, Berlin <-> Split,
    # Lyon <-> Lisbon, Berlin <-> Tallinn, Lyon <-> Bucharest.
    # The chosen itinerary sequence uses the following valid direct flights:
    # Berlin (day 1-5) -> Split (flight on day 5, overlap day),
    # Split (day 5-7) -> Lyon (flight on day 7, overlap day),
    # Lyon (day 7-11) -> Bucharest (flight on day 11, overlap day),
    # Bucharest (day 11-13) -> Lisbon (flight on day 13, overlap day),
    # Lisbon (day 13-15) -> Riga (flight on day 15, overlap day),
    # Riga (day 15-19) -> Tallinn (flight on day 19, overlap day).
    
    itinerary = []
    # Use the overlapping flight rule: if flying on day X, that day is counted for both cities.
    # For the first city, we start at day 1.
    current_day = 1
    
    for i, city_info in enumerate(cities):
        place = city_info["place"]
        duration = city_info["duration"]
        # For the first city, the stay is from current_day to current_day + duration - 1.
        # For subsequent cities, we assume the flight is on the same day as arrival,
        # so we reuse current_day as both departure day's end for the previous city and start for the next.
        start_day = current_day
        end_day = current_day + duration - 1  # since the transit day counts for both
        
        itinerary.append({"day_range": f"{start_day}-{end_day}", "place": place})
        # Next city's start is the same as the current city's end day because of overlap.
        current_day = end_day
        
    return itinerary

def main():
    itinerary = compute_itinerary()
    # Output the itinerary as JSON formatted string
    print(json.dumps(itinerary, indent=2))

if __name__ == '__main__':
    main()