# Define the manual schedule
manual_schedule = [
    ("Haight-Ashbury", 9*60, None),
    ("Nob Hill", 9*60 + 15, "Robert"),
    ("Golden Gate Park", 10*60 + 2, "Steven"),
    ("Alamo Square", 11*60 + 52, "Anthony"),
    ("Pacific Heights", 14*60 + 7, "Sandra"),  # Start at 2:07 PM and meet until 2:45 PM
    ("Fisherman's Wharf", 14*60 + 58, "Kevin")  # Start at 2:58 PM and meet until 4:33 PM
]

# Print the manual schedule
print("SOLUTION:")
for location, time, friend in manual_schedule:
    print(f"{location}: {time//60}:{time%60:02d} {'(' + friend + ')' if friend else ''}")

# Print which friends we meet
met_friends = [friend for _, _, friend in manual_schedule if friend]
print("Met friends:", met_friends)