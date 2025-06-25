import json

def main():
    total_days = 7
    madrid_days = 4
    dublin_days = 3
    tallinn_days = 2
    
    if madrid_days + dublin_days + tallinn_days != total_days + 2:
        result = {"error": "The total days in cities does not match the total days available."}
        print(json.dumps(result))
        return
    
    pure_madrid = madrid_days - 1
    pure_dublin = dublin_days - 2
    pure_tallinn = tallinn_days - 1
    
    if pure_madrid < 0 or pure_dublin < 0 or pure_tallinn < 0:
        result = {"error": "Invalid input: negative pure days calculated."}
        print(json.dumps(result))
        return
    
    segments = []
    
    if pure_madrid > 0:
        start = 1
        end = pure_madrid
        segments.append((start, end, "Madrid"))
    
    travel1_day = pure_madrid + 1
    segments.append((travel1_day, travel1_day, "Madrid and Dublin"))
    
    if pure_dublin > 0:
        start = pure_madrid + 2
        end = start + pure_dublin - 1
        segments.append((start, end, "Dublin"))
    
    travel2_day = pure_madrid + pure_dublin + 2
    segments.append((travel2_day, travel2_day, "Dublin and Tallinn"))
    
    if pure_tallinn > 0:
        start = travel2_day + 1
        end = start + pure_tallinn - 1
        if end > total_days:
            end = total_days
        segments.append((start, end, "Tallinn"))
    
    itinerary_list = []
    for (start, end, place) in segments:
        if start == end:
            day_range_str = "Day {}".format(start)
        else:
            day_range_str = "Day {}-{}".format(start, end)
        itinerary_list.append({"day_range": day_range_str, "place": place})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()