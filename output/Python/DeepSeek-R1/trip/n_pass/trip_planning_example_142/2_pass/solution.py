import json

def main():
    total_days = 7
    madrid_days = 4
    dublin_days = 3
    tallinn_days = 2
    
    # Each travel day is counted as 1 city-day (0.5 per involved city)
    # Total city-days = madrid_days + dublin_days + tallinn_days
    # Calendar days = total_days = pure_days + travel_days
    if madrid_days + dublin_days + tallinn_days != total_days + 2:
        result = {"error": "The total days in cities does not match the total days available."}
        print(json.dumps(result))
        return
    
    # Calculate pure days accounting for travel contributions
    pure_madrid = madrid_days - 0.5  # 1 travel day (departure)
    pure_dublin = dublin_days - 1    # 2 travel days (arrival and departure)
    pure_tallinn = tallinn_days - 0.5  # 1 travel day (arrival)

    # Convert to integer days (since 0.5 days are covered by travel)
    pure_madrid_full = int(pure_madrid)
    pure_dublin_full = int(pure_dublin)
    pure_tallinn_full = int(pure_tallinn)
    
    # Check for negative pure days
    if pure_madrid_full < 0 or pure_dublin_full < 0 or pure_tallinn_full < 0:
        result = {"error": "Invalid input: negative pure days calculated."}
        print(json.dumps(result))
        return
    
    # Build itinerary segments
    segments = []
    current_day = 1
    
    # Madrid segment
    if pure_madrid_full > 0:
        end_madrid = current_day + pure_madrid_full - 1
        segments.append((current_day, end_madrid, "Madrid"))
        current_day = end_madrid + 1
    
    # Travel to Dublin
    segments.append((current_day, current_day, "Madrid and Dublin"))
    current_day += 1
    
    # Dublin segment
    if pure_dublin_full > 0:
        end_dublin = current_day + pure_dublin_full - 1
        segments.append((current_day, end_dublin, "Dublin"))
        current_day = end_dublin + 1
    
    # Travel to Tallinn
    segments.append((current_day, current_day, "Dublin and Tallinn"))
    current_day += 1
    
    # Tallinn segment
    if pure_tallinn_full > 0:
        end_tallinn = current_day + pure_tallinn_full - 1
        # Ensure we don't exceed total days
        if end_tallinn > total_days:
            end_tallinn = total_days
        segments.append((current_day, end_tallinn, "Tallinn"))
    
    # Format itinerary
    itinerary_list = []
    for (start, end, place) in segments:
        if start == end:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range_str, "place": place})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()