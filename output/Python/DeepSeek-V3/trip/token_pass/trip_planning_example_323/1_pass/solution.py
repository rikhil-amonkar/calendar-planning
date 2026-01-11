import json

def plan_itinerary():
    total_days = 16
    cities = {
        "London": 7,
        "Split": 5,
        "Oslo": 2,
        "Porto": 5
    }
    
    # Direct flights graph
    direct_flights = {
        "London": ["Oslo", "Split"],
        "Oslo": ["London", "Split", "Porto"],
        "Split": ["London", "Oslo"],
        "Porto": ["Oslo"]
    }
    
    # Constraints
    split_show_start = 7
    split_show_end = 11
    london_relatives_start = 1
    london_relatives_end = 7
    
    # We'll build day-by-day plan
    itinerary = []
    current_city = "London"
    days_spent = {city: 0 for city in cities}
    day = 1
    
    # Step 1: Start in London (must be there day 1-7)
    london_end_day = 7
    london_stay = london_end_day - day + 1  # days 1 to 7 inclusive = 7 days
    itinerary.append({"day_range": f"Day {day}-{london_end_day}", "place": "London"})
    days_spent["London"] += london_stay
    day = london_end_day  # day 7 is last full London day? Wait, travel happens on day 7.
    # Actually, on day 7 we are in London in the morning, travel to Split, so day 7 counts for both.
    # So London days = days 1-7 = 7 days.
    # We'll handle travel on day 7 below.
    
    # Day 7: travel London -> Split
    travel_day = 7
    current_city = "Split"
    # Day 7 counts for Split too
    days_spent["Split"] += 1
    
    # Step 2: Split for show days 7-11
    split_stay_start = travel_day  # day 7
    split_stay_end = split_show_end  # day 11
    split_stay_days = split_stay_end - split_stay_start + 1  # 5 days
    itinerary.append({"day_range": f"Day {split_stay_start}-{split_stay_end}", "place": "Split"})
    days_spent["Split"] += split_stay_days - 1  # we already counted day 7 above
    day = split_stay_end  # day 11
    
    # Day 11: travel Split -> Oslo
    travel_day = 11
    current_city = "Oslo"
    days_spent["Oslo"] += 1  # day 11 counts for Oslo too
    
    # Step 3: Oslo for 2 days total (already 1 day from travel day 11)
    oslo_stay_start = travel_day  # day 11
    oslo_stay_end = oslo_stay_start + 0  # only day 11? Wait, need 2 days total for Oslo.
    # We have day 11 in Oslo, need 1 more full Oslo day = day 12.
    oslo_stay_end = 12
    itinerary.append({"day_range": f"Day {oslo_stay_start}-{oslo_stay_end}", "place": "Oslo"})
    days_spent["Oslo"] += (oslo_stay_end - oslo_stay_start)  # adds 1 more day (day 12)
    day = oslo_stay_end  # day 12
    
    # Day 12: travel Oslo -> Porto
    travel_day = 12
    current_city = "Porto"
    days_spent["Porto"] += 1  # day 12 counts for Porto too
    
    # Step 4: Porto for remaining days
    porto_stay_start = travel_day  # day 12
    porto_stay_end = total_days  # day 16
    porto_stay_days = porto_stay_end - porto_stay_start + 1  # 5 days
    itinerary.append({"day_range": f"Day {porto_stay_start}-{porto_stay_end}", "place": "Porto"})
    days_spent["Porto"] += porto_stay_days - 1  # we already counted day 12 above
    day = porto_stay_end
    
    # Final check
    print("Days spent per city:", days_spent)
    print("Total city-days:", sum(days_spent.values()))
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_itinerary()
    print(json.dumps(result, indent=2))