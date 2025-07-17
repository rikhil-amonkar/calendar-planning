from z3 import *

# Define the locations and their travel times
locations = [
    "Union Square", "Presidio", "Alamo Square", "Marina District", 
    "Financial District", "Nob Hill", "Sunset District", "Chinatown", 
    "Russian Hill", "North Beach", "Haight-Ashbury"
]

travel_times = {
    ("Union Square", "Presidio"): 24, ("Union Square", "Alamo Square"): 15, 
    ("Union Square", "Marina District"): 18, ("Union Square", "Financial District"): 9, 
    ("Union Square", "Nob Hill"): 9, ("Union Square", "Sunset District"): 27, 
    ("Union Square", "Chinatown"): 7, ("Union Square", "Russian Hill"): 13, 
    ("Union Square", "North Beach"): 10, ("Union Square", "Haight-Ashbury"): 18, 
    ("Presidio", "Union Square"): 22, ("Presidio", "Alamo Square"): 19, 
    ("Presidio", "Marina District"): 11, ("Presidio", "Financial District"): 23, 
    ("Presidio", "Nob Hill"): 18, ("Presidio", "Sunset District"): 15, 
    ("Presidio", "Chinatown"): 21, ("Presidio", "Russian Hill"): 14, 
    ("Presidio", "North Beach"): 18, ("Presidio", "Haight-Ashbury"): 15, 
    ("Alamo Square", "Union Square"): 14, ("Alamo Square", "Presidio"): 17, 
    ("Alamo Square", "Marina District"): 15, ("Alamo Square", "Financial District"): 17, 
    ("Alamo Square", "Nob Hill"): 11, ("Alamo Square", "Sunset District"): 16, 
    ("Alamo Square", "Chinatown"): 15, ("Alamo Square", "Russian Hill"): 13, 
    ("Alamo Square", "North Beach"): 15, ("Alamo Square", "Haight-Ashbury"): 5, 
    ("Marina District", "Union Square"): 16, ("Marina District", "Presidio"): 10, 
    ("Marina District", "Alamo Square"): 15, ("Marina District", "Financial District"): 17, 
    ("Marina District", "Nob Hill"): 12, ("Marina District", "Sunset District"): 19, 
    ("Marina District", "Chinatown"): 15, ("Marina District", "Russian Hill"): 8, 
    ("Marina District", "North Beach"): 11, ("Marina District", "Haight-Ashbury"): 16, 
    ("Financial District", "Union Square"): 9, ("Financial District", "Presidio"): 22, 
    ("Financial District", "Alamo Square"): 17, ("Financial District", "Marina District"): 15, 
    ("Financial District", "Nob Hill"): 8, ("Financial District", "Sunset District"): 30, 
    ("Financial District", "Chinatown"): 5, ("Financial District", "Russian Hill"): 11, 
    ("Financial District", "North Beach"): 7, ("Financial District", "Haight-Ashbury"): 19, 
    ("Nob Hill", "Union Square"): 7, ("Nob Hill", "Presidio"): 17, 
    ("Nob Hill", "Alamo Square"): 11, ("Nob Hill", "Marina District"): 11, 
    ("Nob Hill", "Financial District"): 9, ("Nob Hill", "Sunset District"): 24, 
    ("Nob Hill", "Chinatown"): 6, ("Nob Hill", "Russian Hill"): 5, 
    ("Nob Hill", "North Beach"): 8, ("Nob Hill", "Haight-Ashbury"): 13, 
    ("Sunset District", "Union Square"): 30, ("Sunset District", "Presidio"): 16, 
    ("Sunset District", "Alamo Square"): 17, ("Sunset District", "Marina District"): 21, 
    ("Sunset District", "Financial District"): 30, ("Sunset District", "Nob Hill"): 27, 
    ("Sunset District", "Chinatown"): 29, ("Sunset District", "Russian Hill"): 23, 
    ("Sunset District", "North Beach"): 28, ("Sunset District", "Haight-Ashbury"): 15, 
    ("Chinatown", "Union Square"): 7, ("Chinatown", "Presidio"): 19, 
    ("Chinatown", "Alamo Square"): 17, ("Chinatown", "Marina District"): 12, 
    ("Chinatown", "Financial District"): 5, ("Chinatown", "Nob Hill"): 9, 
    ("Chinatown", "Sunset District"): 29, ("Chinatown", "Russian Hill"): 7, 
    ("Chinatown", "North Beach"): 3, ("Chinatown", "Haight-Ashbury"): 19, 
    ("Russian Hill", "Union Square"): 10, ("Russian Hill", "Presidio"): 14, 
    ("Russian Hill", "Alamo Square"): 15, ("Russian Hill", "Marina District"): 7, 
    ("Russian Hill", "Financial District"): 11, ("Russian Hill", "Nob Hill"): 5, 
    ("Russian Hill", "Sunset District"): 23, ("Russian Hill", "Chinatown"): 9, 
    ("Russian Hill", "North Beach"): 5, ("Russian Hill", "Haight-Ashbury"): 17, 
    ("North Beach", "Union Square"): 7, ("North Beach", "Presidio"): 17, 
    ("North Beach", "Alamo Square"): 16, ("North Beach", "Marina District"): 9, 
    ("North Beach", "Financial District"): 8, ("North Beach", "Nob Hill"): 7, 
    ("North Beach", "Sunset District"): 27, ("North Beach", "Chinatown"): 6, 
    ("North Beach", "Russian Hill"): 4, ("North Beach", "Haight-Ashbury"): 18, 
    ("Haight-Ashbury", "Union Square"): 19, ("Haight-Ashbury", "Presidio"): 15, 
    ("Haight-Ashbury", "Alamo Square"): 5, ("Haight-Ashbury", "Marina District"): 17, 
    ("Haight-Ashbury", "Financial District"): 21, ("Haight-Ashbury", "Nob Hill"): 15, 
    ("Haight-Ashbury", "Sunset District"): 15, ("Haight-Ashbury", "Chinatown"): 19, 
    ("Haight-Ashbury", "Russian Hill"): 17, ("Haight-Ashbury", "North Beach"): 19
}

# Define the meetings and their time windows
meetings = {
    "Kimberly": ("Presidio", 1530, 1600, 15),
    "Elizabeth": ("Alamo Square", 1915, 2015, 15),
    "Joshua": ("Marina District", 1030, 1415, 45),
    "Sandra": ("Financial District", 1930, 2015, 45),
    "Kenneth": ("Nob Hill", 1245, 2145, 30),
    "Betty": ("Sunset District", 1400, 1900, 60),
    "Deborah": ("Chinatown", 1715, 2030, 15),
    "Barbara": ("Russian Hill", 1730, 2145, 120),
    "Steven": ("North Beach", 1745, 2045, 90),
    "Daniel": ("Haight-Ashbury", 1830, 1845, 15)
}

# Convert times to minutes since start of the day
def time_to_minutes(time):
    hours = time // 100
    minutes = time % 100
    return hours * 60