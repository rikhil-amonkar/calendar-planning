import json

def main():
    # Define the segments in the order of travel
    segments = [
        {"place": "Berlin", "duration": 5},   # Days 1-5
        {"place": "Split", "duration": 3},     # Days 5-7
        {"place": "Lyon", "duration": 5},      # Days 7-11
        {"place": "Lisbon", "duration": 3},    # Days 11-13
        {"place": "Bucharest", "duration": 3}, # Days 13-15
        {"place": "Riga", "duration": 5},      # Days 15-19
        {"place": "Tallinn", "duration": 4}    # Days 19-22
    ]
    
    start_day = 1
    itinerary_list = []
    
    for seg in segments:
        end_day = start_day + seg["duration"] - 1
        day_range_str = f"Day {start_day}-{end_day}"
        itinerary_list.append({
            "day_range": day_range_str,
            "place": seg["place"]
        })
        start_day = end_day  # Next segment starts on the same day (travel day)
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()