package com.alexshabanov.groups.categories;

import java.util.List;

public class CategoriesDraft {

  interface CatObj {
  }

  interface CatMorphism {
    CatObj from();
    CatObj to();
  }

  /**
   * A category enumerator, that provides an access to the category's contents.
   */
  interface CatEnumerator {
    List<CatObj> objects();
    List<CatMorphism> morphisms();
    CatMorphism compose(CatMorphism f, CatMorphism g);
  }
}
