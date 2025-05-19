import json

def calculate_itinerary():
    itinerary = []
    
    # Constants for duration in days
    HELSINKI_DAYS = 2
    WARSAW_DAYS = 3
    MADRID_DAYS = 4
    SPLIT_DAYS = 4
    REYKJAVIK_DAYS = 2
    BUDAPEST_DAYS = 4

    # Days allocated
    total_days = 14
    
    # Create an itinerary based on given conditions
    current_day = 1
    
    # Stay in Helsinki for 2 days (Day 1-2)
    itinerary.append({'day_range': 'Day 1-2', 'place': 'Helsinki'})
    
    # Flight to Reykjavik (Day 2)
    itinerary.append({'flying': 'Day 2', 'from': 'Helsinki', 'to': 'Reykjavik'})
    
    # Stay in Reykjavik for 2 days (Day 2-4)
    itinerary.append({'day_range': 'Day 2-4', 'place': 'Reykjavik'})
    
    # Flight to Warsaw (Day 4)
    itinerary.append({'flying': 'Day 4', 'from': 'Reykjavik', 'to': 'Warsaw'})
    
    # Stay in Warsaw for 3 days (Day 4-7)
    itinerary.append({'day_range': 'Day 4-7', 'place': 'Warsaw'})
    
    # Flight to Split (Day 7)
    itinerary.append({'flying': 'Day 7', 'from': 'Warsaw', 'to': 'Split'})
    
    # Stay in Split for 4 days (Day 7-11)
    itinerary.append({'day_range': 'Day 7-11', 'place': 'Split'})
    
    # Flight to Budapest (Day 11)
    itinerary.append({'flying': 'Day 11', 'from': 'Split', 'to': 'Budapest'})
    
    # Stay in Budapest for 4 days (Day 11-14)
    itinerary.append({'day_range': 'Day 11-14', 'place': 'Budapest'})
    
    # Final flight back to Reykjavik from Budapest (not required in final output but logically derived)
    itinerary.append({'flying': 'Day 14', 'from': 'Budapest', 'to': 'Reykjavik'})
    
    return json.dumps(itinerary, indent=4)

if __name__ == "__main__":
    result = calculate_itinerary()
    print(result)