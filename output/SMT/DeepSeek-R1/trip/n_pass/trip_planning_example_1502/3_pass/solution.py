def main():
    itinerary_data = {
        "Santorini": {"arrive": 1, "depart": 3},
        "Valencia": {"arrive": 8, "depart": 11},
        "Madrid": {"arrive": 6, "depart": 7},
        "Seville": {"arrive": 7, "depart": 8},
        "Bucharest": {"arrive": 18, "depart": 20},
        "Vienna": {"arrive": 3, "depart": 6},
        "Riga": {"arrive": 20, "depart": 23},
        "Tallinn": {"arrive": 23, "depart": 27},
        "Krakow": {"arrive": 11, "depart": 15},
        "Frankfurt": {"arrive": 15, "depart": 18}
    }
    
    itinerary_data["Tallinn"]["depart"] = 28
    
    sorted_cities = sorted(
        itinerary_data.items(),
        key=lambda x: x[1]['arrive']
    )
    
    itinerary_list = []
    for city, details in sorted_cities:
        arrive = details['arrive']
        depart = details['depart']
        last_day = depart - 1
        if last_day == arrive:
            day_range_str = f"Day {arrive}"
        else:
            day_range_str = f"Day {arrive}-{last_day}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(result)

if __name__ == '__main__':
    main()