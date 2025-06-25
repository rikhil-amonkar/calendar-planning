import json

def main():
    total_days = 7
    madrid_days = 4
    dublin_days = 3
    tallinn_days = 2
    
    segments = []
    current_day = 1

    # Madrid: full days = total days - 1 (last day is travel day)
    if madrid_days > 1:
        full_madrid = madrid_days - 1
        end = current_day + full_madrid - 1
        segments.append((current_day, end, "Madrid"))
        current_day = end + 1
    else:
        full_madrid = 0

    # Travel from Madrid to Dublin
    if current_day <= total_days and dublin_days > 0:
        segments.append((current_day, current_day, "Madrid and Dublin"))
        current_day += 1

    # Dublin: full days = total days - 2 (first and last days are travel days)
    full_dublin = dublin_days - 2
    if full_dublin > 0:
        end = current_day + full_dublin - 1
        segments.append((current_day, end, "Dublin"))
        current_day = end + 1

    # Travel from Dublin to Tallinn
    if current_day <= total_days and tallinn_days > 0:
        segments.append((current_day, current_day, "Dublin and Tallinn"))
        current_day += 1

    # Tallinn: full days = total days - 1 (first day is travel day)
    full_tallinn = tallinn_days - 1
    if full_tallinn > 0:
        end = current_day + full_tallinn - 1
        segments.append((current_day, end, "Tallinn"))
        current_day = end + 1

    # Convert to required output format
    itinerary_list = []
    for seg in segments:
        start, end, place = seg
        if start == end:
            day_str = f"Day {start}"
        else:
            day_str = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_str, "place": place})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()