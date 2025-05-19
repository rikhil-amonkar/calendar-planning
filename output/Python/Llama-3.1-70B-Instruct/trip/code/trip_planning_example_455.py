import json

def calculate_trip_plan(reykjavik_days, riga_days, warsaw_days, istanbul_days, krakow_days, friend_meeting_window, wedding_window):
    total_days = reykjavik_days + riga_days + warsaw_days + istanbul_days + krakow_days

    # Calculate the number of days for each city, considering the friend meeting window in Riga
    riga_start_day = 1
    riga_end_day = riga_start_day + riga_days - 1
    friend_meeting_day = (friend_meeting_window[0] + friend_meeting_window[1]) // 2

    # Ensure Riga is visited first to meet a friend
    if friend_meeting_day < riga_start_day or friend_meeting_day > riga_end_day:
        raise ValueError("Friend meeting day does not fall within the Riga visit window")

    # Calculate the day ranges for Istanbul
    istanbul_start_day = riga_end_day + 1
    istanbul_end_day = istanbul_start_day + istanbul_days - 1
    wedding_day = (wedding_window[0] + wedding_window[1]) // 2

    # Ensure Istanbul is visited to attend the wedding
    if wedding_day < istanbul_start_day or wedding_day > istanbul_end_day:
        raise ValueError("Wedding day does not fall within the Istanbul visit window")

    # Calculate the day ranges for Warsaw
    warsaw_start_day = istanbul_end_day + 1
    warsaw_end_day = warsaw_start_day + warsaw_days - 1

    # Calculate the day ranges for Reykjavik
    reykjavik_start_day = warsaw_end_day + 1
    reykjavik_end_day = reykjavik_start_day + reykjavik_days - 1

    # Calculate the day ranges for Krakow
    krakow_start_day = reykjavik_end_day + 1
    krakow_end_day = krakow_start_day + krakow_days - 1

    # Check if the total days add up correctly
    if krakow_end_day!= total_days:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {riga_start_day}-{riga_end_day}', 'place': 'Riga'},
        {'flying': f'Day {riga_end_day}-{riga_end_day}', 'from': 'Riga', 'to': 'Istanbul'},
        {'day_range': f'Day {istanbul_start_day}-{istanbul_end_day}', 'place': 'Istanbul'},
        {'flying': f'Day {istanbul_end_day}-{istanbul_end_day}', 'from': 'Istanbul', 'to': 'Warsaw'},
        {'day_range': f'Day {warsaw_start_day}-{warsaw_end_day}', 'place': 'Warsaw'},
        {'flying': f'Day {warsaw_end_day}-{warsaw_end_day}', 'from': 'Warsaw', 'to': 'Reykjavik'},
        {'day_range': f'Day {reykjavik_start_day}-{reykjavik_end_day}', 'place': 'Reykjavik'},
        {'flying': f'Day {reykjavik_end_day}-{reykjavik_end_day}', 'from': 'Reykjavik', 'to': 'Krakow'},
        {'day_range': f'Day {krakow_start_day}-{krakow_end_day}', 'place': 'Krakow'}
    ]

    return trip_plan

def main():
    reykjavik_days = 7
    riga_days = 2
    warsaw_days = 3
    istanbul_days = 6
    krakow_days = 7
    friend_meeting_window = (1, 2)
    wedding_window = (2, 7)

    trip_plan = calculate_trip_plan(reykjavik_days, riga_days, warsaw_days, istanbul_days, krakow_days, friend_meeting_window, wedding_window)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()