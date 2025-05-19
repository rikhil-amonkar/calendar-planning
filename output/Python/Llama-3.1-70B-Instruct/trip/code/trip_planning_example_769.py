import json

def calculate_trip_plan(porto_days, prague_days, reykjavik_days, santorini_days, amsterdam_days, munich_days, friend_meeting_window, wedding_window, conference_window):
    total_days = porto_days + prague_days + reykjavik_days + santorini_days + amsterdam_days + munich_days

    # Calculate the number of days for each city, considering the friend meeting window in Munich
    munich_start_day = 7
    munich_end_day = munich_start_day + munich_days - 1
    friend_meeting_day = (friend_meeting_window[0] + friend_meeting_window[1]) // 2

    # Ensure Munich is visited to meet a friend
    if friend_meeting_day < munich_start_day or friend_meeting_day > munich_end_day:
        raise ValueError("Friend meeting day does not fall within the Munich visit window")

    # Calculate the day ranges for Porto
    porto_start_day = 1
    porto_end_day = porto_start_day + porto_days - 1

    # Calculate the day ranges for Prague
    prague_start_day = porto_end_day + 1
    prague_end_day = prague_start_day + prague_days - 1

    # Calculate the day ranges for Reykjavik
    reykjavik_start_day = prague_end_day + 1
    reykjavik_end_day = reykjavik_start_day + reykjavik_days - 1
    wedding_day = (wedding_window[0] + wedding_window[1]) // 2

    # Ensure Reykjavik is visited to attend the wedding
    if wedding_day < reykjavik_start_day or wedding_day > reykjavik_end_day:
        raise ValueError("Wedding day does not fall within the Reykjavik visit window")

    # Calculate the day ranges for Santorini
    santorini_start_day = reykjavik_end_day + 1
    santorini_end_day = santorini_start_day + santorini_days - 1

    # Calculate the day ranges for Amsterdam
    amsterdam_start_day = santorini_end_day + 1
    amsterdam_end_day = amsterdam_start_day + amsterdam_days - 1
    conference_day = (conference_window[0] + conference_window[1]) // 2

    # Ensure Amsterdam is visited to attend the conference
    if conference_day < amsterdam_start_day or conference_day > amsterdam_end_day:
        raise ValueError("Conference day does not fall within the Amsterdam visit window")

    # Check if the total days add up correctly
    if amsterdam_end_day!= total_days:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {porto_start_day}-{porto_end_day}', 'place': 'Porto'},
        {'flying': f'Day {porto_end_day}-{porto_end_day}', 'from': 'Porto', 'to': 'Prague'},
        {'day_range': f'Day {prague_start_day}-{prague_end_day}', 'place': 'Prague'},
        {'flying': f'Day {prague_end_day}-{prague_end_day}', 'from': 'Prague', 'to': 'Reykjavik'},
        {'day_range': f'Day {reykjavik_start_day}-{reykjavik_end_day}', 'place': 'Reykjavik'},
        {'flying': f'Day {reykjavik_end_day}-{reykjavik_end_day}', 'from': 'Reykjavik', 'to': 'Santorini'},
        {'day_range': f'Day {santorini_start_day}-{santorini_end_day}', 'place': 'Santorini'},
        {'flying': f'Day {santorini_end_day}-{santorini_end_day}', 'from': 'Santorini', 'to': 'Amsterdam'},
        {'day_range': f'Day {amsterdam_start_day}-{amsterdam_start_day}', 'place': 'Amsterdam'},
        {'flying': f'Day {amsterdam_start_day}-{amsterdam_start_day}', 'from': 'Amsterdam', 'to': 'Munich'},
        {'day_range': f'Day {munich_start_day}-{munich_end_day}', 'place': 'Munich'},
        {'flying': f'Day {munich_end_day}-{munich_end_day}', 'from': 'Munich', 'to': 'Amsterdam'},
        {'day_range': f'Day {munich_end_day+1}-{total_days}', 'place': 'Amsterdam'}
    ]

    return trip_plan

def main():
    porto_days = 5
    prague_days = 4
    reykjavik_days = 4
    santorini_days = 2
    amsterdam_days = 2
    munich_days = 4
    friend_meeting_window = (7, 10)
    wedding_window = (4, 7)
    conference_window = (14, 15)

    trip_plan = calculate_trip_plan(porto_days, prague_days, reykjavik_days, santorini_days, amsterdam_days, munich_days, friend_meeting_window, wedding_window, conference_window)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()