import json

def main():
    total_days = 15
    paris_days = 6
    madrid_days = 7
    bucharest_days = 2
    seville_days = 3

    segments = []
    start = 1
    end = start + madrid_days - 1
    segments.append((start, end, "Madrid"))
    
    start = end
    end = start + seville_days - 1
    segments.append((start, end, "Seville"))
    
    start = end
    end = start + paris_days - 1
    segments.append((start, end, "Paris"))
    
    start = end
    end = start + bucharest_days - 1
    segments.append((start, end, "Bucharest"))
    
    itinerary_list = []
    for seg in segments:
        s, e, city = seg
        if s == e:
            day_range_str = f"Day {s}"
        else:
            day_range_str = f"Day {s}-{e}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()