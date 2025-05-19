import json

def calculate_trip_plan(hamburg_days, zurich_days, helsinki_days, bucharest_days, split_days, wedding_window, conference_window):
    total_days = hamburg_days + zurich_days + helsinki_days + bucharest_days + split_days

    # Calculate the number of days for each city, considering the wedding window in Zurich
    zurich_start_day = 1
    zurich_end_day = zurich_start_day + zurich_days - 1
    wedding_day = (wedding_window[0] + wedding_window[1]) // 2

    # Ensure Zurich is visited first to attend the wedding
    if wedding_day < zurich_start_day or wedding_day > zurich_end_day:
        raise ValueError("Wedding day does not fall within the Zurich visit window")

    # Calculate the day ranges for Hamburg
    hamburg_start_day = zurich_end_day + 1
    hamburg_end_day = hamburg_start_day + hamburg_days - 1

    # Calculate the day ranges for Helsinki
    helsinki_start_day = hamburg_end_day + 1
    helsinki_end_day = helsinki_start_day + helsinki_days - 1

    # Calculate the day ranges for Bucharest
    bucharest_start_day = helsinki_end_day + 1
    bucharest_end_day = bucharest_start_day + bucharest_days - 1

    # Calculate the day ranges for Split
    split_start_day = bucharest_end_day + 1
    split_end_day = split_start_day + split_days - 1
    conference_day = (conference_window[0] + conference_window[1]) // 2

    # Ensure Split is visited to attend the conference
    if conference_day < split_start_day or conference_day > split_end_day:
        raise ValueError("Conference day does not fall within the Split visit window")

    # Check if the total days add up correctly
    if split_end_day!= total_days:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {zurich_start_day}-{zurich_end_day}', 'place': 'Zurich'},
        {'flying': f'Day {zurich_end_day}-{zurich_end_day}', 'from': 'Zurich', 'to': 'Hamburg'},
        {'day_range': f'Day {hamburg_start_day}-{hamburg_end_day}', 'place': 'Hamburg'},
        {'flying': f'Day {hamburg_end_day}-{hamburg_end_day}', 'from': 'Hamburg', 'to': 'Helsinki'},
        {'day_range': f'Day {helsinki_start_day}-{helsinki_end_day}', 'place': 'Helsinki'},
        {'flying': f'Day {helsinki_end_day}-{helsinki_end_day}', 'from': 'Helsinki', 'to': 'Bucharest'},
        {'day_range': f'Day {bucharest_start_day}-{bucharest_end_day}', 'place': 'Bucharest'},
        {'flying': f'Day {bucharest_end_day}-{bucharest_end_day}', 'from': 'Bucharest', 'to': 'Split'},
        {'day_range': f'Day {split_start_day}-{split_end_day}', 'place': 'Split'}
    ]

    return trip_plan

def main():
    hamburg_days = 2
    zurich_days = 3
    helsinki_days = 2
    bucharest_days = 2
    split_days = 7
    wedding_window = (1, 3)
    conference_window = (4, 10)

    trip_plan = calculate_trip_plan(hamburg_days, zurich_days, helsinki_days, bucharest_days, split_days, wedding_window, conference_window)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()