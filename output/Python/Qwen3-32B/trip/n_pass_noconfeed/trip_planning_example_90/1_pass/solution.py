import json

def main():
    # Define trip constraints
    durations = {
        'Naples': 5,
        'Vienna': 7,
        'Vilnius': 7
    }
    
    # Define itinerary order based on constraints
    itinerary_order = ['Naples', 'Vienna', 'Vilnius']
    
    # Calculate day ranges
    current_start = 1
    itinerary = []
    
    for city in itinerary_order:
        days_in_city = durations[city]
        end_day = current_start + days_in_city - 1
        day_range = f"Day {current_start}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
        current_start = end_day
    
    # Format and output result
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()