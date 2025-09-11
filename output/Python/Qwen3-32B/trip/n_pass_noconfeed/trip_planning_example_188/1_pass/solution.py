import json

def main():
    # Input constraints
    required_days = {
        'Brussels': 2,
        'Barcelona': 7,
        'Split': 5
    }
    order = ['Brussels', 'Barcelona', 'Split']
    
    itinerary = []
    prev_end = 0
    
    for city in order:
        if prev_end == 0:
            start_day = 1
        else:
            start_day = prev_end
        days_needed = required_days[city]
        end_day = start_day + days_needed - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
        prev_end = end_day
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()