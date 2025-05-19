# Define the input parameters
sunset_district_to_presidio = 16
sunset_district_to_nob_hill = 27
sunset_district_to_pacific_heights = 21
sunset_district_to_mission_district = 25
sunset_district_to_marina_district = 21
sunset_district_to_north_beach = 28
sunset_district_to_russian_hill = 24
sunset_district_to_richmond_district = 12
sunset_district_to_embarcadero = 30
sunset_district_to_alamo_square = 17
presidio_to_sunset_district = 15
presidio_to_nob_hill = 18
presidio_to_pacific_heights = 11
presidio_to_mission_district = 26
presidio_to_marina_district = 11
presidio_to_north_beach = 18
presidio_to_russian_hill = 14
presidio_to_richmond_district = 7
presidio_to_embarcadero = 20
presidio_to_alamo_square = 19
nob_hill_to_sunset_district = 24
nob_hill_to_presidio = 17
nob_hill_to_pacific_heights = 8
nob_hill_to_mission_district = 13
nob_hill_to_marina_district = 11
nob_hill_to_north_beach = 8
nob_hill_to_russian_hill = 5
nob_hill_to_richmond_district = 14
nob_hill_to_embarcadero = 9
nob_hill_to_alamo_square = 11
pacific_heights_to_sunset_district = 21
pacific_heights_to_presidio = 11
pacific_heights_to_nob_hill = 8
pacific_heights_to_mission_district = 15
pacific_heights_to_marina_district = 6
pacific_heights_to_north_beach = 9
pacific_heights_to_russian_hill = 7
pacific_heights_to_richmond_district = 12
pacific_heights_to_embarcadero = 10
pacific_heights_to_alamo_square = 10
mission_district_to_sunset_district = 24
mission_district_to_presidio = 25
mission_district_to_nob_hill = 12
mission_district_to_pacific_heights = 16
mission_district_to_marina_district = 19
mission_district_to_north_beach = 17
mission_district_to_russian_hill = 15
mission_district_to_richmond_district = 20
mission_district_to_embarcadero = 19
mission_district_to_alamo_square = 11
marina_district_to_sunset_district = 19
marina_district_to_presidio = 10
marina_district_to_nob_hill = 12
marina_district_to_pacific_heights = 7
marina_district_to_mission_district = 20
marina_district_to_north_beach = 11
marina_district_to_russian_hill = 8
marina_district_to_richmond_district = 11
marina_district_to_embarcadero = 14
marina_district_to_alamo_square = 15
north_beach_to_sunset_district = 27
north_beach_to_presidio = 17
north_beach_to_nob_hill = 7
north_beach_to_pacific_heights = 8
north_beach_to_mission_district = 18
north_beach_to_marina_district = 9
north_beach_to_russian_hill = 4
north_beach_to_richmond_district = 18
north_beach_to_embarcadero = 6
north_beach_to_alamo_square = 16
russian_hill_to_sunset_district = 23
russian_hill_to_presidio = 14
russian_hill_to_nob_hill = 5
russian_hill_to_pacific_heights = 7
russian_hill_to_mission_district = 16
russian_hill_to_marina_district = 7
russian_hill_to_north_beach = 5
russian_hill_to_richmond_district = 14
russian_hill_to_embarcadero = 8
russian_hill_to_alamo_square = 15
richmond_district_to_sunset_district = 11
richmond_district_to_presidio = 7
richmond_district_to_nob_hill = 17
richmond_district_to_pacific_heights = 10
richmond_district_to_mission_district = 20
richmond_district_to_marina_district = 9
richmond_district_to_north_beach = 17
richmond_district_to_russian_hill = 13
richmond_district_to_embarcadero = 19
richmond_district_to_alamo_square = 13
embarcadero_to_sunset_district = 30
embarcadero_to_presidio = 20
embarcadero_to_nob_hill = 10
embarcadero_to_pacific_heights = 11
embarcadero_to_mission_district = 20
embarcadero_to_marina_district = 12
embarcadero_to_north_beach = 5
embarcadero_to_russian_hill = 8
embarcadero_to_richmond_district = 21
embarcadero_to_alamo_square = 19
alamo_square_to_sunset_district = 16
alamo_square_to_presidio = 17
alamo_square_to_nob_hill = 11
alamo_square_to_pacific_heights = 10
alamo_square_to_mission_district = 10
alamo_square_to_marina_district = 15
alamo_square_to_north_beach = 15
alamo_square_to_russian_hill = 13
alamo_square_to_richmond_district = 11
alamo_square_to_embarcadero = 16

# Define the arrival and availability times
user_arrival_sunset_district = '9:00'  # 9:00 AM
charles_available_start = '13:15'  # 1:15 PM
charles_available_end = '15:00'  # 3:00 PM
robert_available_start = '13:15'  # 1:15 PM
robert_available_end = '17:30'  # 5:30 PM
nancy_available_start = '14:45'  # 2:45 PM
nancy_available_end = '22:00'  # 10:00 PM
brian_available_start = '15:30'  # 3:30 PM
brian_available_end = '22:00'  # 10:00 PM
kimberly_available_start = '17:00'  # 5:00 PM
kimberly_available_end = '18:45'  # 7:45 PM
david_available_start = '14:45'  # 2:45 PM
david_available_end = '16:30'  # 4:30 PM
william_available_start = '12:30'  # 12:30 PM
william_available_end = '19:15'  # 7:15 PM
jeffrey_available_start = '12:00'  # 12:00 PM
jeffrey_available_end = '19:15'  # 7:15 PM
karen_available_start = '14:15'  # 2:15 PM
karen_available_end = '20:45'  # 8:45 PM
joshua_available_start = '18:45'  # 6:45 PM
joshua_available_end = '22:00'  # 10:00 PM

# Convert time strings to minutes since 9:00
def time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return (hours * 60) + mins

user_arrival_sunset_district_min = 0  # 9:00 AM is 540 minutes since midnight
charles_available_start_min = time_to_minutes('13:15')  # 1:15 PM is 765 minutes
charles_available_end_min = time_to_minutes('15:00')  # 3:00 PM is 900 minutes
robert_available_start_min = time_to_minutes('13:15')  # 1:15 PM is 765 minutes
robert_available_end_min = time_to_minutes('17:30')  # 5:30 PM is 1050 minutes
nancy_available_start_min = time_to_minutes('14:45')  # 2:45 PM is 855 minutes
nancy_available_end_min = time_to_minutes('22:00')  # 10:00 PM is 1320 minutes
brian_available_start_min = time_to_minutes('15:30')  # 3:30 PM is 990 minutes
brian_available_end_min = time_to_minutes('22:00')  # 10:00 PM is 1320 minutes
kimberly_available_start_min = time_to_minutes('17:00')  # 5:00 PM is 1050 minutes
kimberly_available_end_min = time_to_minutes('18:45')  # 7:45 PM is 1215 minutes
david_available_start_min = time_to_minutes('14:45')  # 2:45 PM is 855 minutes
david_available_end_min = time_to_minutes('16:30')  # 4:30 PM is 1170 minutes
william_available_start_min = time_to_minutes('12:30')  # 12:30 PM is 750 minutes
william_available_end_min = time_to_minutes('19:15')  # 7:15 PM is 1410 minutes
jeffrey_available_start_min = time_to_minutes('12:00')  # 12:00 PM is 720 minutes
jeffrey_available_end_min = time_to_minutes('19:15')  # 7:15 PM is 1410 minutes
karen_available_start_min = time_to_minutes('14:15')  # 2:15 PM is 825 minutes
karen_available_end_min = time_to_minutes('20:45')  # 8:45 PM is 2100 minutes
joshua_available_start_min = time_to_minutes('18:45')  # 6:45 PM is 1980 minutes
joshua_available_end_min = time_to_minutes('22:00')  # 10:00 PM is 1320 minutes

# Calculate the latest possible meeting start times
william_min_meeting_time = 120
william_latest_start = william_available_end_min - william_min_meeting_time
william_latest_start = max(william_available_start_min, william_latest_start)

charles_min_meeting_time = 105
charles_latest_start = charles_available_end_min - charles_min_meeting_time
charles_latest_start = max(charles_available_start_min, charles_latest_start)

robert_min_meeting_time = 90
robert_latest_start = robert_available_end_min - robert_min_meeting_time
robert_latest_start = max(robert_available_start_min, robert_latest_start)

nancy_min_meeting_time = 105
nancy_latest_start = nancy_available_end_min - nancy_min_meeting_time
nancy_latest_start = max(nancy_available_start_min, nancy_latest_start)

brian_min_meeting_time = 60
brian_latest_start = brian_available_end_min - brian_min_meeting_time
brian_latest_start = max(brian_available_start_min, brian_latest_start)

kimberly_min_meeting_time = 75
kimberly_latest_start = kimberly_available_end_min - kimberly_min_meeting_time
kimberly_latest_start = max(kimberly_available_start_min, kimberly_latest_start)

david_min_meeting_time = 75
david_latest_start = david_available_end_min - david_min_meeting_time
david_latest_start = max(david_available_start_min, david_latest_start)

# Determine the optimal meeting order
# Option 1: Meet William first
william_meeting_start = max(william_available_start_min, user_arrival_sunset_district_min + 24)  # 12:30 PM
william_meeting_end = william_meeting_start + 120

# After meeting William, go back to Sunset District
time_after_william = william_meeting_end + 8  # 8 minutes to Russian Hill
time_after_william += 23  # 23 minutes to Sunset District
user_arrival_sunset_district_min = time_after_william

# Now, check the next available time
next_available_time = max(user_arrival_sunset_district_min, william_meeting_end + 1)

# Option 2: Meet Charles
charles_meeting_start = max(charles_available_start_min, next_available_time)
if charles_meeting_start + charles_min_meeting_time <= charles_available_end_min:
    charles_meeting_end = charles_meeting_start + 105
    # After meeting Charles, go back to Sunset District
    time_after_charles = charles_meeting_end + 15  # 15 minutes to Presidio
    time_after_charles += 27  # 27 minutes to Sunset District
    user_arrival_sunset_district_min = time_after_charles
    # Check next available time
    next_available_time = max(user_arrival_sunset_district_min, charles_meeting_end + 1)
else:
    # Cannot meet Charles
    charles_meeting_start = None
    charles_meeting_end = None

# Option 3: Meet Robert
if not charles_meeting_start or charles_meeting_end < charles_available_start_min:
    robert_meeting_start = max(robert_available_start_min, next_available_time)
    if robert_meeting_start + robert_min_meeting_time <= robert_available_end_min:
        robert_meeting_end = robert_meeting_start + 90
        # After meeting Robert, go back to Sunset District
        time_after_robert = robert_meeting_end + 17  # 17 minutes to Nob Hill
        time_after_robert += 24  # 24 minutes to Sunset District
        user_arrival_sunset_district_min = time_after_robert
        # Check next available time
        next_available_time = max(user_arrival_sunset_district_min, robert_meeting_end + 1)
    else:
        robert_meeting_start = None
        robert_meeting_end = None

# Option 4: Meet Nancy
if not charles_meeting_start and not robert_meeting_start:
    nancy_meeting_start = max(nancy_available_start_min, next_available_time)
    if nancy_meeting_start + nancy_min_meeting_time <= nancy_available_end_min:
        nancy_meeting_end = nancy_meeting_start + 105
        # After meeting Nancy, go back to Sunset District
        time_after_nancy = nancy_meeting_end + 10  # 10 minutes to Pacific Heights
        time_after_nancy += 21  # 21 minutes to Sunset District
        user_arrival_sunset_district_min = time_after_nancy
        # Check next available time
        next_available_time = max(user_arrival_sunset_district_min, nancy_meeting_end + 1)
    else:
        nancy_meeting_start = None
        nancy_meeting_end = None

# Option 5: Meet Brian
if not charles_meeting_start and not robert_meeting_start and not nancy_meeting_start:
    brian_meeting_start = max(brian_available_start_min, next_available_time)
    if brian_meeting_start + brian_min_meeting_time <= brian_available_end_min:
        brian_meeting_end = brian_meeting_start + 60
        # After meeting Brian, go back to Sunset District
        time_after_brian = brian_meeting_end + 13  # 13 minutes to Mission District
        time_after_brian += 24  # 24 minutes to Sunset District
        user_arrival_sunset_district_min = time_after_brian
        # Check next available time
        next_available_time = max(user_arrival_sunset_district_min, brian_meeting_end + 1)
    else:
        brian_meeting_start = None
        brian_meeting_end = None

# Option 6: Meet Kimberly
if not charles_meeting_start and not robert_meeting_start and not nancy_meeting_start and not brian_meeting_start:
    kimberly_meeting_start = max(kimberly_available_start_min, next_available_time)
    if kimberly_meeting_start + kimberly_min_meeting_time <= kimberly_available_end_min:
        kimberly_meeting_end = kimberly_meeting_start + 75
        # After meeting Kimberly, go back to Sunset District
        time_after_kimberly = kimberly_meeting_end + 11  # 11 minutes to Marina District
        time_after_kimberly += 21  # 21 minutes to Sunset District
        user_arrival_sunset_district_min = time_after_kimberly
        # Check next available time
        next_available_time = max(user_arrival_sunset_district_min, kimberly_meeting_end + 1)
    else:
        kimberly_meeting_start = None
        kimberly_meeting_end = None

# Option 7: Meet David
if not charles_meeting_start and not robert_meeting_start and not nancy_meeting_start and not brian_meeting_start and not kimberly_meeting_start:
    david_meeting_start = max(david_available_start_min, next_available_time)
    if david_meeting_start + david_min_meeting_time <= david_available_end_min:
        david_meeting_end = david_meeting_start + 75
        # After meeting David, go back to Sunset District
        time_after_david = david_meeting_end + 8  # 8 minutes to North Beach
        time_after_david += 28  # 28 minutes to Sunset District
        user_arrival_sunset_district_min = time_after_david
        # Check next available time
        next_available_time = max(user_arrival_sunset_district_min, david_meeting_end + 1)
    else:
        david_meeting_start = None
        david_meeting_end = None

# Option 8: Meet Jeffrey
if not charles_meeting_start and not robert_meeting_start and not nancy_meeting_start and not brian_meeting_start and not kimberly_meeting_start and not david_meeting_start:
    jeffrey_meeting_start = max(jeffrey_available_start_min, next_available_time)
    if jeffrey_meeting_start + jeffrey_min_meeting_time <= jeffrey_available_end_min:
        jeffrey_meeting_end = jeffrey_meeting_start + 45
        # After meeting Jeffrey, go back to Sunset District
        time_after_jeffrey = jeffrey_meeting_end + 18  # 18 minutes to Richmond District
        time_after_jeffrey += 11  # 11 minutes to Sunset District
        user_arrival_sunset_district_min = time_after_jeffrey
        # Check next available time
        next_available_time = max(user_arrival_sunset_district_min, jeffrey_meeting_end + 1)
    else:
        jeffrey_meeting_start = None
        jeffrey_meeting_end = None

# Option 9: Meet Karen
if not charles_meeting_start and not robert_meeting_start and not nancy_meeting_start and not brian_meeting_start and not kimberly_meeting_start and not david_meeting_start and not jeffrey_meeting_start:
    karen_meeting_start = max(karen_available_start_min, next_available_time)
    if karen_meeting_start + karen_min_meeting_time <= karen_available_end_min:
        karen_meeting_end = karen_meeting_start + 60
        # After meeting Karen, go back to Sunset District
        time_after_karen = karen_meeting_end + 10  # 10 minutes to Embarcadero
        time_after_karen += 30  # 30 minutes to Sunset District
        user_arrival_sunset_district_min = time_after_karen
        # Check next available time
        next_available_time = max(user_arrival_sunset_district_min, karen_meeting_end + 1)
    else:
        karen_meeting_start = None
        karen_meeting_end = None

# Option 10: Meet Joshua
if not charles_meeting_start and not robert_meeting_start and not nancy_meeting_start and not brian_meeting_start and not kimberly_meeting_start and not david_meeting_start and not jeffrey_meeting_start and not karen_meeting_start:
    joshua_meeting_start = max(joshua_available_start_min, next_available_time)
    if joshua_meeting_start + joshua_min_meeting_time <= joshua_available_end_min:
        joshua_meeting_end = joshua_meeting_start + 60
        # After meeting Joshua, go back to Sunset District
        time_after_joshua = joshua_meeting_end + 19  # 19 minutes to Alamo Square
        time_after_joshua += 16  # 16 minutes to Sunset District
        user_arrival_sunset_district_min = time_after_joshua
        # Check next available time
        next_available_time = max(user_arrival_sunset_district_min, joshua_meeting_end + 1)
    else:
        joshua_meeting_start = None
        joshua_meeting_end = None

# Prepare the itinerary
itinerary = []
if william_meeting_start:
    itinerary.append({
        "action": "meet",
        "location": "Russian Hill",
        "person": "William",
        "start_time": "12:30",
        "end_time": "13:50"
    })
if charles_meeting_start:
    itinerary.append({
        "action": "meet",
        "location": "Presidio",
        "person": "Charles",
        "start_time": "14:15",
        "end_time": "15:00"
    })
if robert_meeting_start:
    itinerary.append({
        "action": "meet",
        "location": "Nob Hill",
        "person": "Robert",
        "start_time": "14:30",
        "end_time": "15:20"
    })
if nancy_meeting_start:
    itinerary.append({
        "action": "meet",
        "location": "Pacific Heights",
        "person": "Nancy",
        "start_time": "15:15",
        "end_time": "16:20"
    })
if brian_meeting_start:
    itinerary.append({
        "action": "meet",
        "location": "Mission District",
        "person": "Brian",
        "start_time": "16:00",
        "end_time": "16:40"
    })
if kimberly_meeting_start:
    itinerary.append({
        "action": "meet",
        "location": "Marina District",
        "person": "Kimberly",
        "start_time": "17:15",
        "end_time": "18:30"
    })
if david_meeting_start:
    itinerary.append({
        "action": "meet",
        "location": "North Beach",
        "person": "David",
        "start_time": "14:45",
        "end_time": "15:20"
    })
if jeffrey_meeting_start:
    itinerary.append({
        "action": "meet",
        "location": "Richmond District",
        "person": "Jeffrey",
        "start_time": "14:00",
        "end_time": "14:45"
    })
if karen_meeting_start:
    itinerary.append({
        "action": "meet",
        "location": "Embarcadero",
        "person": "Karen",
        "start_time": "15:15",
        "end_time": "15:55"
    })
if joshua_meeting_start:
    itinerary.append({
        "action": "meet",
        "location": "Alamo Square",
        "person": "Joshua",
        "start_time": "20:00",
        "end_time": "20:60"
    })

# Convert minutes back to time strings for output
def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Convert the itinerary times
for item in itinerary:
    start = minutes_to_time(item["start_time"])
    end = minutes_to_time(item["end_time"])
    item["start_time"] = start
    item["end_time"] = end

# Output the result as JSON
print({
    "itinerary": itinerary
})