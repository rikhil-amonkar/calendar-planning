import json

def main():
    total_days = 7
    madrid_days = 4
    dublin_days = 3
    tallinn_days = 2
    
    segments = []
    current_day = 1

    # Madrid segment
    full_madrid = madrid_days - 1
    if full_madrid > 0:
        end = current_day + full_madrid - 1
        segments.append((current_day, end, "Madrid"))
        current_day = end + 1
    else:
        full_madrid = 0

    # Travel from Madrid to Dublin
    if dublin_days > 0:
        if current_day <= total_days:
            segments.append((current_day, current_day, "Madrid and Dublin"))
            current_day += 1

    # Dublin segment
    full_dublin = dublin_days - 2
    if full_dublin < 0:
        full_dublin = 0
    if full_dublin > 0:
        end = current_day + full_dublin - 1
        if end > total_days:
            end = total_days
        if current_day <= end:
            segments.append((current_day, end, "Dublin"))
            current_day = end + 1

    # Travel from Dublin to Tallinn
    if tallinn_days > 0:
        if current_day <= total_days:
            segments.append((current_day, current_day, "Dublin and Tallinn"))
            current_day += 1

    # Tallinn segment
    full_tallinn = tallinn_days - 1
    if full_tallinn < 0:
        full_tallinn = 0
    if full_tallinn > 0:
        end = current_day + full_tallinn - 1
        if end > total_days:
            end = total_days
        if current_day <= end:
            segments.append((current_day, end, "Tallinn"))
            current_day = end + 1

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