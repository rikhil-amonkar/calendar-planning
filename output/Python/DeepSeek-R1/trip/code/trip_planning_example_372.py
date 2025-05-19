import json

def main():
    cities = {
        "Madrid": {"days": 4, "flights": ["Porto", "Seville"]},
        "Seville": {"days": 2, "flights": ["Madrid", "Porto"]},
        "Porto": {"days": 3, "flights": ["Madrid", "Seville", "Stuttgart"]},
        "Stuttgart": {"days": 7, "flights": ["Porto"]}
    }
    
    itinerary = []
    current_day = 1
    
    # Madrid (Day 1-4)
    itinerary.append({"day_range": f"Day {current_day}-4", "place": "Madrid"})
    current_day = 4
    
    # Transition to Seville
    seville_end = current_day + cities["Seville"]["days"]
    itinerary.append({"day_range": f"Day {current_day}-{seville_end}", "place": "Seville"})
    current_day = seville_end
    
    # Transition to Porto
    porto_end = current_day + cities["Porto"]["days"]
    itinerary.append({"day_range": f"Day {current_day}-{porto_end}", "place": "Porto"})
    current_day = porto_end
    
    # Transition to Stuttgart (must cover day 7-13)
    stuttgart_start = 7
    stuttgart_end = 13
    if current_day > stuttgart_start:
        stuttgart_start = current_day
    itinerary.append({"day_range": f"Day {stuttgart_start}-{stuttgart_end}", "place": "Stuttgart"})
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()