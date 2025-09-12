name = str(model.eval(z3.Select(name_array, h))).split('.')[1]
house_style = str(model.eval(z3.Select(house_style_array, h))).split('.')[1]
music_genre = str(model.eval(z3.Select(music_genre_array, h))).split('.')[1]
hobby = str(model.eval(z3.Select(hobby_array, h))).split('.')[1]