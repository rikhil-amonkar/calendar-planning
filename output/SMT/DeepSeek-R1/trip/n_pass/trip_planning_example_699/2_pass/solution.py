def main():
    fixed_plan = {
        1: "Hamburg",
        2: "Dublin",
        3: "Dublin",
        4: "Dublin",
        5: "Dublin",
        6: "Dublin",
        7: "Mykonos",
        8: "Mykonos",
        9: "Reykjavik",
        10: "Reykjavik",
        11: "Mykonos",
        12: "London",
        13: "London",
        14: "London",
        15: "London",
        16: "London"
    }
    
    segments = []
    current_place = None
    start_day = None
    
    for day in range(1, 17):
        place = fixed_plan[day]
        if current_place is None:
            current_place = place
            start_day = day
        elif current_place == place:
            continue
        else:
            end_day = day - 1
            if start_day == end_day:
                day_range_str = f"Day {start_day}"
            else:
                day_range_str = f"Day {start_day}-{end_day}"
            segments.append({"day_range": day_range_str, "place": current_place})
            current_place = place
            start_day = day
    
    end_day = 16
    if start_day == end_day:
        day_range_str = f"Day {start_day}"
    else:
        day_range_str = f"Day {start_day}-{end_day}"
    segments.append({"day_range": day_range_str, "place": current_place})
    
    result = {"itinerary": segments}
    return result

if __name__ == "__main__":
    result = main()
    print(result)