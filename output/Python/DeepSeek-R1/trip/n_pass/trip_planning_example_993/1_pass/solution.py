import json

def main():
    # City requirements
    req = {
        'Riga': 2,
        'Frankfurt': 3,
        'Amsterdam': 2,
        'Vilnius': 5,
        'London': 2,
        'Stockholm': 3,
        'Bucharest': 4
    }
    
    # Precomputed city order based on constraints
    order = [
        'London',
        'Amsterdam',
        'Bucharest',
        'Riga',
        'Vilnius',
        'Frankfurt',
        'Stockholm'
    ]
    
    start_day = 1
    itinerary_list = []
    for city in order:
        duration = req[city]
        end_day = start_day + duration - 1
        day_range_str = f"Day {start_day}-{end_day}"
        itinerary_list.append({
            "day_range": day_range_str,
            "place": city
        })
        start_day = end_day  # Next city starts on the same day the current city ends (travel day)
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()