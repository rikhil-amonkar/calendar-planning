import json

def calculate_trip_plan(helsinki_days, warsaw_days, madrid_days, split_days, reykjavik_days, budapest_days, workshop_window, visit_relatives_window, meet_friend_window):
    total_days = helsinki_days + warsaw_days + madrid_days + split_days + reykjavik_days + budapest_days

    # Calculate the number of days for each city, considering the workshop window in Helsinki
    helsinki_start_day = 1
    helsinki_end_day = helsinki_start_day + helsinki_days - 1
    workshop_day = (workshop_window[0] + workshop_window[1]) // 2

    # Ensure Helsinki is visited first to attend the workshop
    if workshop_day < helsinki_start_day or workshop_day > helsinki_end_day:
        raise ValueError("Workshop day does not fall within the Helsinki visit window")

    # Calculate the day ranges for Budapest
    budapest_start_day = helsinki_end_day + 1
    budapest_end_day = budapest_start_day + budapest_days - 1

    # Calculate the day ranges for Warsaw
    warsaw_start_day = budapest_end_day + 1
    warsaw_end_day = warsaw_start_day + warsaw_days - 1
    visit_relatives_day = (visit_relatives_window[0] + visit_relatives_window[1]) // 2

    # Ensure Warsaw is visited to visit relatives
    if visit_relatives_day < warsaw_start_day or visit_relatives_day > warsaw_end_day:
        raise ValueError("Visit relatives day does not fall within the Warsaw visit window")

    # Calculate the day ranges for Reykjavik
    reykjavik_start_day = warsaw_end_day + 1
    reykjavik_end_day = reykjavik_start_day + reykjavik_days - 1
    meet_friend_day = (meet_friend_window[0] + meet_friend_window[1]) // 2

    # Ensure Reykjavik is visited to meet a friend
    if meet_friend_day < reykjavik_start_day or meet_friend_day > reykjavik_end_day:
        raise ValueError("Meet friend day does not fall within the Reykjavik visit window")

    # Calculate the day ranges for Madrid
    madrid_start_day = reykjavik_end_day + 1
    madrid_end_day = madrid_start_day + madrid_days - 1

    # Calculate the day ranges for Split
    split_start_day = madrid_end_day + 1
    split_end_day = split_start_day + split_days - 1

    # Check if the total days add up correctly
    if split_end_day!= total_days:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {helsinki_start_day}-{helsinki_end_day}', 'place': 'Helsinki'},
        {'flying': f'Day {helsinki_end_day}-{helsinki_end_day}', 'from': 'Helsinki', 'to': 'Budapest'},
        {'day_range': f'Day {budapest_start_day}-{budapest_end_day}', 'place': 'Budapest'},
        {'flying': f'Day {budapest_end_day}-{budapest_end_day}', 'from': 'Budapest', 'to': 'Warsaw'},
        {'day_range': f'Day {warsaw_start_day}-{warsaw_end_day}', 'place': 'Warsaw'},
        {'flying': f'Day {warsaw_end_day}-{warsaw_end_day}', 'from': 'Warsaw', 'to': 'Reykjavik'},
        {'day_range': f'Day {reykjavik_start_day}-{reykjavik_end_day}', 'place': 'Reykjavik'},
        {'flying': f'Day {reykjavik_end_day}-{reykjavik_end_day}', 'from': 'Reykjavik', 'to': 'Madrid'},
        {'day_range': f'Day {madrid_start_day}-{madrid_end_day}', 'place': 'Madrid'},
        {'flying': f'Day {madrid_end_day}-{madrid_end_day}', 'from': 'Madrid', 'to': 'Split'},
        {'day_range': f'Day {split_start_day}-{split_end_day}', 'place': 'Split'}
    ]

    return trip_plan

def main():
    helsinki_days = 2
    warsaw_days = 3
    madrid_days = 4
    split_days = 4
    reykjavik_days = 2
    budapest_days = 4
    workshop_window = (1, 2)
    visit_relatives_window = (9, 11)
    meet_friend_window = (8, 9)

    trip_plan = calculate_trip_plan(helsinki_days, warsaw_days, madrid_days, split_days, reykjavik_days, budapest_days, workshop_window, visit_relatives_window, meet_friend_window)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()