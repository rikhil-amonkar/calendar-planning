import json

def main():
    total_days = 10
    wedding_city = "Krakow"
    wedding_start = 9
    wedding_end = 10
    
    city_days = {
        "Dubrovnik": 7,
        "Frankfurt": 3,
        "Krakow": 2
    }
    
    route_order = ["Dubrovnik", "Frankfurt", "Krakow"]
    
    segments = []
    
    krakow_start = wedding_start
    krakow_end = wedding_end
    segments.append(("Krakow", krakow_start, krakow_end))
    
    frankfurt_end = krakow_start
    frankfurt_days = city_days["Frankfurt"]
    frankfurt_start = frankfurt_end - frankfurt_days + 1
    segments.insert(0, ("Frankfurt", frankfurt_start, frankfurt_end))
    
    dubrovnik_end = frankfurt_start
    dubrovnik_days = city_days["Dubrovnik"]
    dubrovnik_start = dubrovnik_end - dubrovnik_days + 1
    segments.insert(0, ("Dubrovnik", dubrovnik_start, dubrovnik_end))
    
    itinerary_list = []
    for city, start, end in segments:
        day_range_str = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()