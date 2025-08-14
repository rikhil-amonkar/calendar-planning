# Define the manual schedule
manual_schedule = [
    ("Haight-Ashbury", 9*60, None),
    ("Nob Hill", 9*60 + 15, "Robert"),
    ("Golden Gate Park", 10*60 + 2, "Steven"),
    ("Alamo Square", 11*60 + 52, "Anthony"),
    ("Pacific Heights", 12*60 + 7, "Sandra"),
    ("Fisherman's Wharf", 12*60 + 52, "Kevin")
]

# Print the manual schedule
print("SOLUTION:")
for location, time, friend in manual_schedule:
    print(f"{location}: {time//60}:{time%60:02d} {'(' + friend + ')' if friend else ''}")

# Print which friends we meet
met_friends = [friend for _, _, friend in manual_schedule if friend]
print("Met friends:", met_friends)