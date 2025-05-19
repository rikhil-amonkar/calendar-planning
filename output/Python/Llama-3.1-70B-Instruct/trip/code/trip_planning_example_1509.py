import json

def calculate_trip_plan(paris_days, warsaw_days, krakow_days, tallinn_days, riga_days, copenhagen_days, helsinki_days, oslo_days, santorini_days, lyon_days, friend_meeting_window, workshop_window, wedding_window, meet_friend_window, visit_relatives_window):
    total_days = paris_days + warsaw_days + krakow_days + tallinn_days + riga_days + copenhagen_days + helsinki_days + oslo_days + santorini_days + lyon_days

    # Calculate the number of days for each city, considering the friend meeting window in Paris
    paris_start_day = 1
    paris_end_day = paris_start_day + paris_days - 1
    friend_meeting_day = (friend_meeting_window[0] + friend_meeting_window[1]) // 2

    # Ensure Paris is visited first to meet friends
    if friend_meeting_day < paris_start_day or friend_meeting_day > paris_end_day:
        raise ValueError("Friend meeting day does not fall within the Paris visit window")

    # Calculate the day ranges for Lyon
    lyon_start_day = paris_end_day + 1
    lyon_end_day = lyon_start_day + lyon_days - 1

    # Calculate the day ranges for Oslo
    oslo_start_day = lyon_end_day + 1
    oslo_end_day = oslo_start_day + oslo_days - 1

    # Calculate the day ranges for Santorini
    santorini_start_day = oslo_end_day + 1
    santorini_end_day = santorini_start_day + santorini_days - 1
    visit_relatives_day = (visit_relatives_window[0] + visit_relatives_window[1]) // 2

    # Ensure Santorini is visited to visit relatives
    if visit_relatives_day < santorini_start_day or visit_relatives_day > santorini_end_day:
        raise ValueError("Visit relatives day does not fall within the Santorini visit window")

    # Calculate the day ranges for Copenhagen
    copenhagen_start_day = santorini_end_day + 1
    copenhagen_end_day = copenhagen_start_day + copenhagen_days - 1

    # Calculate the day ranges for Warsaw
    warsaw_start_day = copenhagen_end_day + 1
    warsaw_end_day = warsaw_start_day + warsaw_days - 1

    # Calculate the day ranges for Krakow
    krakow_start_day = warsaw_end_day + 1
    krakow_end_day = krakow_start_day + krakow_days - 1
    workshop_day = (workshop_window[0] + workshop_window[1]) // 2

    # Ensure Krakow is visited to attend the workshop
    if workshop_day < krakow_start_day or workshop_day > krakow_end_day:
        raise ValueError("Workshop day does not fall within the Krakow visit window")

    # Calculate the day ranges for Helsinki
    helsinki_start_day = krakow_end_day + 1
    helsinki_end_day = helsinki_start_day + helsinki_days - 1
    meet_friend_day = (meet_friend_window[0] + meet_friend_window[1]) // 2

    # Ensure Helsinki is visited to meet a friend
    if meet_friend_day < helsinki_start_day or meet_friend_day > helsinki_end_day:
        raise ValueError("Meet friend day does not fall within the Helsinki visit window")

    # Calculate the day ranges for Tallinn
    tallinn_start_day = helsinki_end_day + 1
    tallinn_end_day = tallinn_start_day + tallinn_days - 1

    # Calculate the day ranges for Riga
    riga_start_day = tallinn_end_day + 1
    riga_end_day = riga_start_day + riga_days - 1
    wedding_day = (wedding_window[0] + wedding_window[1]) // 2

    # Ensure Riga is visited last to attend the wedding
    if wedding_day < riga_start_day or wedding_day > riga_end_day:
        raise ValueError("Wedding day does not fall within the Riga visit window")

    # Check if the total days add up correctly
    if riga_end_day!= total_days:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {paris_start_day}-{paris_end_day}', 'place': 'Paris'},
        {'flying': f'Day {paris_end_day}-{paris_end_day}', 'from': 'Paris', 'to': 'Lyon'},
        {'day_range': f'Day {lyon_start_day}-{lyon_end_day}', 'place': 'Lyon'},
        {'flying': f'Day {lyon_end_day}-{lyon_end_day}', 'from': 'Lyon', 'to': 'Oslo'},
        {'day_range': f'Day {oslo_start_day}-{oslo_end_day}', 'place': 'Oslo'},
        {'flying': f'Day {oslo_end_day}-{oslo_end_day}', 'from': 'Oslo', 'to': 'Santorini'},
        {'day_range': f'Day {santorini_start_day}-{santorini_end_day}', 'place': 'Santorini'},
        {'flying': f'Day {santorini_end_day}-{santorini_end_day}', 'from': 'Santorini', 'to': 'Copenhagen'},
        {'day_range': f'Day {copenhagen_start_day}-{copenhagen_end_day}', 'place': 'Copenhagen'},
        {'flying': f'Day {copenhagen_end_day}-{copenhagen_end_day}', 'from': 'Copenhagen', 'to': 'Warsaw'},
        {'day_range': f'Day {warsaw_start_day}-{warsaw_end_day}', 'place': 'Warsaw'},
        {'flying': f'Day {warsaw_end_day}-{warsaw_end_day}', 'from': 'Warsaw', 'to': 'Krakow'},
        {'day_range': f'Day {krakow_start_day}-{krakow_end_day}', 'place': 'Krakow'},
        {'flying': f'Day {krakow_end_day}-{krakow_end_day}', 'from': 'Krakow', 'to': 'Helsinki'},
        {'day_range': f'Day {helsinki_start_day}-{helsinki_end_day}', 'place': 'Helsinki'},
        {'flying': f'Day {helsinki_end_day}-{helsinki_end_day}', 'from': 'Helsinki', 'to': 'Tallinn'},
        {'day_range': f'Day {tallinn_start_day}-{tallinn_end_day}', 'place': 'Tallinn'},
        {'flying': f'Day {tallinn_end_day}-{tallinn_end_day}', 'from': 'Tallinn', 'to': 'Riga'},
        {'day_range': f'Day {riga_start_day}-{riga_end_day}', 'place': 'Riga'}
    ]

    return trip_plan

def main():
    paris_days = 5
    warsaw_days = 2
    krakow_days = 2
    tallinn_days = 2
    riga_days = 2
    copenhagen_days = 5
    helsinki_days = 5
    oslo_days = 5
    santorini_days = 2
    lyon_days = 4
    friend_meeting_window = (4, 8)
    workshop_window = (17, 18)
    wedding_window = (23, 24)
    meet_friend_window = (18, 22)
    visit_relatives_window = (12, 13)

    trip_plan = calculate_trip_plan(paris_days, warsaw_days, krakow_days, tallinn_days, riga_days, copenhagen_days, helsinki_days, oslo_days, santorini_days, lyon_days, friend_meeting_window, workshop_window, wedding_window, meet_friend_window, visit_relatives_window)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()