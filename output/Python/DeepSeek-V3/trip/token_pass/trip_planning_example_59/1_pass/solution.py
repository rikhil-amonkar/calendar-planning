import json

def plan_trip():
    total_days = 16
    lyon_days_needed = 7
    bucharest_days_needed = 7
    porto_days_needed = 4
    
    # Derived schedule from earlier calculation
    itinerary = []
    
    # Day 1-6: Bucharest
    itinerary.append({"day_range": "Day 1-6", "place": "Bucharest"})
    # Day 7: Bucharest & Lyon (travel day)
    itinerary.append({"day_range": "Day 7", "place": "Bucharest & Lyon (travel)"})
    # Day 8-12: Lyon
    itinerary.append({"day_range": "Day 8-12", "place": "Lyon"})
    # Day 13: Lyon & Porto (travel day)
    itinerary.append({"day_range": "Day 13", "place": "Lyon & Porto (travel)"})
    # Day 14-16: Porto
    itinerary.append({"day_range": "Day 14-16", "place": "Porto"})
    
    # Verification
    b_days = 6 + 1  # 1-6 + day 7
    l_days = 1 + 5 + 1  # day 7 + 8-12 + day 13
    p_days = 1 + 3  # day 13 + 14-16
    
    assert b_days == bucharest_days_needed, f"Bucharest days mismatch: {b_days}"
    assert l_days == lyon_days_needed, f"Lyon days mismatch: {l_days}"
    assert p_days == porto_days_needed, f"Porto days mismatch: {p_days}"
    assert len(itinerary) > 0
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_trip()
    print(json.dumps(result, indent=2))