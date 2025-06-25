import json

def main():
    total_days = 7
    madrid_days = 4
    dublin_days = 3
    tallinn_days = 2
    
    # Calculate pure days accounting for travel contributions
    pure_madrid = madrid_days - 0.5  # 1 travel day (departure)
    pure_dublin = dublin_days - 1    # 2 travel days (arrival and departure)
    pure_tallinn = tallinn_days - 0.5  # 1 travel day (arrival)

    # Convert to integer days (truncate fractional parts)
    pure_madrid_full = int(pure_madrid)
    pure_dublin_full = int(pure_dublin)
    pure_tallinn_full = int(pure_tallinn)
    
    # Build itinerary segments
    segments = []
    current_day = 1
    
    # Madrid segment
    if pure_madrid_full > 0:
        end_madrid = current_day + pure_madrid_full - 1
        segments.append((current_day, end_madrid, "Madrid"))
        current_day = end_madrid + 1
    
    # Travel to Dublin
    if current_day <= total_days:
        segments.append((current_day, current_day, "Madrid and Dublin"))
        current_day += 1
    
    # Dublin segment
    if pure_dublin_full > 0 and current_day <= total_days:
        end_dublin = current_day + pure_dublin_full - 1
        if end_dublin > total_days:
            end_dublin = total_days
        segments.append((current_day, end_dublin, "Dublin"))
        current_day = end_dublin + 1
    
    # Travel to Tallinn
    if current_day <= total_days:
        segments.append((current_day, current_day, "Dublin and Tallinn"))
        current_day += 1
    
    # Tallinn segment (only if within total days)
    if pure_tallinn_full > 0 and current_day <= total_days:
        end_tallinn = current_day + pure_tallinn_full - 1
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