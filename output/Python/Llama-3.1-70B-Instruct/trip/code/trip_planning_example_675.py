import json

def calculate_trip_plan(dubrovnik_days, split_days, milan_days, porto_days, krakow_days, munich_days, friend_meeting_window, wedding_window, annual_show_window):
    total_days = dubrovnik_days + split_days + milan_days + porto_days + krakow_days + munich_days

    # Calculate the number of days for each city, considering the annual show window in Munich
    munich_start_day = 4
    munich_end_day = munich_start_day + munich_days - 1
    annual_show_day = (annual_show_window[0] + annual_show_window[1]) // 2

    # Ensure Munich is visited to attend the annual show
    if annual_show_day < munich_start_day or annual_show_day > munich_end_day:
        raise ValueError("Annual show day does not fall within the Munich visit window")

    # Calculate the day ranges for Dubrovnik
    dubrovnik_start_day = 1
    dubrovnik_end_day = dubrovnik_start_day + dubrovnik_days - 1

    # Calculate the day ranges for Krakow
    krakow_start_day = munich_end_day + 1
    krakow_end_day = krakow_start_day + krakow_days - 1
    friend_meeting_day = (friend_meeting_window[0] + friend_meeting_window[1]) // 2

    # Ensure Krakow is visited to meet friends
    if friend_meeting_day < krakow_start_day or friend_meeting_day > krakow_end_day:
        raise ValueError("Friend meeting day does not fall within the Krakow visit window")

    # Calculate the day ranges for Split
    split_start_day = krakow_end_day + 1
    split_end_day = split_start_day + split_days - 1

    # Calculate the day ranges for Milan
    milan_start_day = split_end_day + 1
    milan_end_day = milan_start_day + milan_days - 1
    wedding_day = (wedding_window[0] + wedding_window[1]) // 2

    # Ensure Milan is visited to attend the wedding
    if wedding_day < milan_start_day or wedding_day > milan_end_day:
        raise ValueError("Wedding day does not fall within the Milan visit window")

    # Calculate the day ranges for Porto
    porto_start_day = milan_end_day + 1
    porto_end_day = porto_start_day + porto_days - 1

    # Check if the total days add up correctly
    if porto_end_day!= total_days:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {dubrovnik_start_day}-{dubrovnik_end_day}', 'place': 'Dubrovnik'},
        {'flying': f'Day {dubrovnik_end_day}-{dubrovnik_end_day}', 'from': 'Dubrovnik', 'to': 'Munich'},
        {'day_range': f'Day {munich_start_day}-{munich_end_day}', 'place': 'Munich'},
        {'flying': f'Day {munich_end_day}-{munich_end_day}', 'from': 'Munich', 'to': 'Krakow'},
        {'day_range': f'Day {krakow_start_day}-{krakow_end_day}', 'place': 'Krakow'},
        {'flying': f'Day {krakow_end_day}-{krakow_end_day}', 'from': 'Krakow', 'to': 'Split'},
        {'day_range': f'Day {split_start_day}-{split_end_day}', 'place': 'Split'},
        {'flying': f'Day {split_end_day}-{split_end_day}', 'from': 'Split', 'to': 'Milan'},
        {'day_range': f'Day {milan_start_day}-{milan_end_day}', 'place': 'Milan'},
        {'flying': f'Day {milan_end_day}-{milan_end_day}', 'from': 'Milan', 'to': 'Porto'},
        {'day_range': f'Day {porto_start_day}-{porto_end_day}', 'place': 'Porto'}
    ]

    return trip_plan

def main():
    dubrovnik_days = 4
    split_days = 3
    milan_days = 3
    porto_days = 4
    krakow_days = 2
    munich_days = 5
    friend_meeting_window = (8, 9)
    wedding_window = (11, 13)
    annual_show_window = (4, 8)

    trip_plan = calculate_trip_plan(dubrovnik_days, split_days, milan_days, porto_days, krakow_days, munich_days, friend_meeting_window, wedding_window, annual_show_window)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()