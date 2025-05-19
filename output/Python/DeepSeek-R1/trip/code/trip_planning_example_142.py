import json

def plan_trip():
    cities = {"Madrid": 4, "Dublin": 3, "Tallinn": 2}
    flights = {"Madrid": ["Dublin"], "Dublin": ["Madrid", "Tallinn"], "Tallinn": ["Dublin"]}
    itinerary = []
    day = 1
    
    # Madrid phase
    madrid_end = day + cities["Madrid"] - 1
    itinerary.append({"day_range": f"Day {day}-{madrid_end}", "place": "Madrid"})
    day = madrid_end
    
    # Dublin phase with flight day overlap
    dublin_end = day + cities["Dublin"] - 1
    itinerary.append({"day_range": f"Day {day}-{dublin_end}", "place": "Dublin"})
    day = dublin_end
    
    # Tallinn phase with workshop constraint check
    tallinn_end = day + cities["Tallinn"] - 1
    if tallinn_end != 7:
        return {"itinerary": []}
    itinerary.append({"day_range": f"Day {day}-{tallinn_end}", "place": "Tallinn"})
    
    # Verify flight connections
    valid = (itinerary[1]["place"] in flights[itinerary[0]["place"]] and 
             itinerary[2]["place"] in flights[itinerary[1]["place"]])
    return {"itinerary": itinerary} if valid else {"itinerary": []}

print(json.dumps(plan_trip()))