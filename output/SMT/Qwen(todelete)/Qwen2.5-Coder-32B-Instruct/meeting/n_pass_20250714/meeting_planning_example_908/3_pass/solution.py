from datetime import datetime, timedelta

# Define the schedule manually
schedule = [
    ("Mark", datetime(2023, 10, 1, 8, 15), datetime(2023, 10, 1, 8, 45)),
    ("Betty", datetime(2023, 10, 1, 8, 45), datetime(2023, 10, 1, 9, 0)),
    ("Brian", datetime(2023, 10, 1, 9, 21), datetime(2023, 10, 1, 9, 51)),
    ("Ashley", datetime(2023, 10, 1, 9, 50), datetime(2023, 10, 1, 10, 35)),
    ("Joseph", datetime(2023, 10, 1, 10, 45), datetime(2023, 10, 1, 12, 15)),
    ("Stephanie", datetime(2023, 10, 1, 12, 15), datetime(2023, 10, 1, 13, 30)),
    ("Lisa", datetime(2023, 10, 1, 15, 30), datetime(2023, 10, 1, 16, 15)),
    ("Patricia", datetime(2023, 10, 1, 16, 30), datetime(2023, 10, 1, 18, 30)),
    ("Karen", datetime(2023, 10, 1, 18, 30), datetime(2023, 10, 1, 20, 15)),
]

# Print the final schedule
print("SOLUTION:")
for friend_name, start_time, end_time in schedule:
    print(f"{friend_name}: {start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')}")