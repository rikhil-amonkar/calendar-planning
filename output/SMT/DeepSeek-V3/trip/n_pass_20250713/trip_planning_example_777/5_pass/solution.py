import json

def create_itinerary():
    itinerary = [
        # Day 1: Start in Reykjavik
        {"day_range": "Day 1", "place": "Reykjavik"},
        
        # Day 2: Fly to Vienna (show day 1/2)
        {"day_range": "Day 2", "place": "Reykjavik"},
        {"day_range": "Day 2", "place": "Vienna"},
        
        # Day 3: Vienna (show day 2/2)
        {"day_range": "Day 3", "place": "Vienna"},
        
        # Day 4: Fly to Helsinki (friends day 1/3)
        {"day_range": "Day 4", "place": "Vienna"},
        {"day_range": "Day 4", "place": "Helsinki"},
        
        # Days 5-6: Helsinki (friends days 2-3/3)
        {"day_range": "Day 5", "place": "Helsinki"},
        {"day_range": "Day 6", "place": "Helsinki"},
        
        # Day 6: Fly to Riga
        {"day_range": "Day 6", "place": "Riga"},
        
        # Days 7-8: Riga
        {"day_range": "Day 7", "place": "Riga"},
        {"day_range": "Day 8", "place": "Riga"},
        
        # Day 8: Fly to Tallinn (wedding day 1/5)
        {"day_range": "Day 8", "place": "Tallinn"},
        
        # Days 9-11: Tallinn (wedding days 2-4/5)
        {"day_range": "Day 9-11", "place": "Tallinn"},
        
        # Day 12: Tallinn (wedding day 5/5)
        {"day_range": "Day 12", "place": "Tallinn"},
        
        # Day 12: Fly to Dublin
        {"day_range": "Day 12", "place": "Dublin"},
        
        # Days 13-15: Dublin
        {"day_range": "Day 13-15", "place": "Dublin"}
    ]
    
    # Verify city day counts
    city_days = {
        "Dublin": 0,
        "Helsinki": 0,
        "Riga": 0,
        "Reykjavik": 0,
        "Vienna": 0,
        "Tallinn": 0
    }
    
    for entry in itinerary:
        day_range = entry["day_range"]
        place = entry["place"]
        if '-' in day_range:
            start, end = map(int, day_range.replace("Day ", "").split('-'))
            days = end - start + 1
        else:
            days = 1
        city_days[place] += days
    
    # Verify constraints
    assert city_days["Dublin"] == 4  # Days 12-15 (4 days)
    assert city_days["Helsinki"] == 3  # Days 4-6
    assert city_days["Riga"] == 3  # Days 6-8
    assert city_days["Reykjavik"] == 2  # Days 1-2
    assert city_days["Vienna"] == 2  # Days 2-4
    assert city_days["Tallinn"] == 5  # Days 8-12
    
    # Verify total days
    total_days = 0
    for entry in itinerary:
        day_range = entry["day_range"]
        if '-' in day_range:
            start, end = map(int, day_range.replace("Day ", "").split('-'))
            total_days += end - start + 1
        else:
            total_days += 1
    
    # Adjust for flight days (where days are counted twice)
    # We have 4 flight days (days 2,4,6,8,12)
    # Each flight day counts as 2 entries but only 1 day
    flight_days = {2,4,6,8,12}
    total_days = total_days - len(flight_days)
    assert total_days == 15
    
    return {"itinerary": itinerary}

result = create_itinerary()
print(json.dumps(result, indent=2))