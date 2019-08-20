---
layout: archive
title: "CV"
permalink: /cv/
author_profile: true
redirect_from:
  - /resume
---

{% include base_path %}

Education
======
* B.S. in Computer Science, Universidade Federal de Ouro Preto, 2005.
* M.S. in Computer Science, Universidade Federal de Minas Gerais, 2007.
* Ph.D in Computer Science, Universidade Federal de Minas Gerais, 2013.

Work experience
======
* Spring 2008: Lecturer
  * Universidade Federal de Ouro Preto
  
Publications
======
  <ul>{% for post in site.publications reverse %}
    {% include archive-single-cv.html %}
  {% endfor %}</ul>
  
Talks
======
  <ul>{% for post in site.talks reverse %}
    {% include archive-single-talk-cv.html %}
  {% endfor %}</ul>
  
Teaching
======
  <ul>{% for post in site.teaching %}
    {% include archive-single-cv.html %}
  {% endfor %}</ul>
